require('dotenv').config();
const express  = require('express');
const http     = require('http');
const { Server } = require('socket.io');
const cors     = require('cors');
const crypto   = require('crypto');
const mongoose = require('mongoose');
const jwt      = require('jsonwebtoken');
const { QUESTIONS_DB } = require('./questions');
const { BIBLE_QUESTIONS } = require('./bibleQuestions');
const User     = require('./models/User');
const Admin    = require('./models/Admin');

const app    = express();
const server = http.createServer(app);

const io = new Server(server, {
  cors: {
    origin: '*',
    methods: ['GET', 'POST'],
  },
  // Prevent clients from hammering with huge payloads
  maxHttpBufferSize: 1e4,   // 10 KB max per message
  pingTimeout: 20000,
  pingInterval: 10000,
});

app.use(cors());
app.use(express.json({ limit: '10kb' }));
app.get('/', (_, res) => res.send('QuizDuel Server running ✅'));

// ─── In-memory state ──────────────────────────────────────────────────────────
const lobby       = new Map();   // deviceId → { socketId, username, joinedAt }
const matches     = new Map();   // matchId  → Match
const devices     = new Map();   // deviceId → socketId  (for reconnects)
const sessions    = new Map();   // sessionToken → { deviceId, socketId, createdAt }
const violations  = new Map();   // deviceId → count

// Rate-limit: track event timestamps per socket
const rateLimits  = new Map();   // socketId → { join_lobby: [timestamps], submit_answer: [...] }

// Spectator / view sockets
const spectators  = new Set();   // set of socketIds for view-only clients

// Leaderboard: username → { username, wins, stage }
const leaderboard = new Map();

// specialSession: set by admin via REST or admin socket event
let specialSession = { active: true, questions: [] };

// Required lobby size for special session (normal sessions pair immediately)
const SPECIAL_LOBBY_REQUIRED = 10;

// ─── Tournament Registration System ──────────────────────────────────────────
// Players enter username before tournament, wait until admin starts, then all play
const registeredPlayers = new Map(); // deviceId → { username, deviceId, joinedAt, socketId }
let tournamentConfig = {
  scheduledDate: null,            // ISO string — when set, registration mode is active
  tournamentStarted: false,       // Has the admin started the tournament?
};

// Registration mode is ON only when admin has set a scheduled date
function isRegistrationMode() {
  return tournamentConfig.scheduledDate !== null && !tournamentConfig.tournamentStarted;
}

function canStartPlaying() {
  return tournamentConfig.tournamentStarted;
}

// Auto-start timer reference
let autoStartTimer = null;

// Reusable function to start the tournament and pair all players
function startTournament() {
  if (tournamentConfig.tournamentStarted) return { error: 'Tournament already started' };
  if (registeredPlayers.size < 2) return { error: 'Need at least 2 registered players' };

  tournamentConfig.tournamentStarted = true;

  // Shuffle registered players and pair them into 1v1 Bible quiz matches
  const players = [...registeredPlayers.values()];
  for (let i = players.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [players[i], players[j]] = [players[j], players[i]];
  }

  const matchPairs = [];
  for (let i = 0; i < players.length - 1; i += 2) {
    const p1 = players[i];
    const p2 = players[i + 1];

    const match = createMatch(
      { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
      { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
      true // isSpecialSession = Bible quiz
    );

    matchPairs.push({
      matchId: match.matchId,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });

    const s1 = io.sockets.sockets.get(p1.socketId);
    const s2 = io.sockets.sockets.get(p2.socketId);

    const matchPayload = {
      matchId: match.matchId,
      matchSeed: match.seed,
      questions: match.questions,
    };

    if (s1) {
      s1.join(match.matchId);
      s1.emit('match_found', {
        ...matchPayload,
        opponent: { username: p2.username, id: p2.deviceId },
      });
    }
    if (s2) {
      s2.join(match.matchId);
      s2.emit('match_found', {
        ...matchPayload,
        opponent: { username: p1.username, id: p1.deviceId },
      });
    }

    console.log(`[tournament] Paired: ${p1.username} vs ${p2.username} → ${match.matchId}`);
  }

  // Handle odd player — give them a bye
  if (players.length % 2 !== 0) {
    const byePlayer = players[players.length - 1];
    const s = io.sockets.sockets.get(byePlayer.socketId);
    if (s) {
      s.emit('tournament_bye', {
        message: 'You got a bye this round! You advance automatically.',
        username: byePlayer.username,
      });
    }
    console.log(`[tournament] Bye: ${byePlayer.username} (odd player count)`);
  }

  io.emit('tournament_started', {
    message: 'Tournament is starting!',
    playerCount: registeredPlayers.size,
    matchCount: matchPairs.length,
  });

  console.log(`[tournament] Started with ${registeredPlayers.size} players, ${matchPairs.length} matches`);
  return { ok: true, playerCount: registeredPlayers.size, matches: matchPairs };
}

// Schedule auto-start timer for a tournament
function scheduleAutoStart(scheduledDate) {
  // Clear any existing timer
  if (autoStartTimer) {
    clearTimeout(autoStartTimer);
    autoStartTimer = null;
  }

  const startTime = new Date(scheduledDate).getTime();
  const delay = startTime - Date.now();

  if (delay <= 0) {
    // Time already passed — start immediately if possible
    console.log('[tournament] Scheduled time already passed — auto-starting now');
    const result = startTournament();
    if (result.error) console.log(`[tournament] Auto-start failed: ${result.error}`);
    return;
  }

  console.log(`[tournament] Auto-start scheduled in ${Math.round(delay / 1000)}s (${scheduledDate})`);
  autoStartTimer = setTimeout(() => {
    console.log('[tournament] ⏰ Auto-starting tournament now!');
    const result = startTournament();
    if (result.error) {
      console.log(`[tournament] Auto-start failed: ${result.error}`);
    }
  }, delay);
}

// ─── Security helpers ─────────────────────────────────────────────────────────

// Rate limiter: allow max `limit` events per `windowMs`
function isRateLimited(socketId, event, limit = 5, windowMs = 5000) {
  if (!rateLimits.has(socketId)) rateLimits.set(socketId, {});
  const buckets = rateLimits.get(socketId);
  if (!buckets[event]) buckets[event] = [];
  const now = Date.now();
  buckets[event] = buckets[event].filter(t => now - t < windowMs);
  if (buckets[event].length >= limit) return true;
  buckets[event].push(now);
  return false;
}

// Track violation; auto-disconnect after threshold
function recordViolation(socket, reason) {
  const deviceId = socket.data.deviceId || socket.id;
  const count = (violations.get(deviceId) || 0) + 1;
  violations.set(deviceId, count);
  console.warn(`[⚠️  VIOLATION] ${deviceId} — ${reason} (total: ${count})`);
  socket.emit('security_violation', { reason, count });
  if (count >= 3) {
    console.warn(`[🔴 BAN] ${deviceId} exceeded violation limit — disconnecting`);
    socket.emit('security_ban', { reason: 'Too many violations. You have been disconnected.' });
    setTimeout(() => socket.disconnect(true), 500);
  }
}

// Validate session token — one active socket per session
function validateSession(socket, sessionToken, deviceId) {
  const existing = sessions.get(sessionToken);
  if (existing && existing.socketId !== socket.id && existing.deviceId !== deviceId) {
    // Different device/socket trying to reuse token → duplicate session
    return false;
  }
  sessions.set(sessionToken, { deviceId, socketId: socket.id, createdAt: Date.now() });
  return true;
}

// Answer timing validation (ms)
const MIN_ANSWER_MS = 350; // impossible to answer faster than this


// ─── Helpers ──────────────────────────────────────────────────────────────────

// Simple deterministic hash → number (mulberry32 seed)
function hashStr(str) {
  let h = 0x811c9dc5;
  for (let i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  return h;
}

function mulberry32(seed) {
  let s = seed >>> 0;
  return () => {
    s += 0x6d2b79f5;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t ^= t + Math.imul(t ^ (t >>> 7), 61 | t);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function seededShuffle(arr, seedStr) {
  const rng = mulberry32(hashStr(String(seedStr)));
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// Remove stale lobby entries (> 60s — give players time to find opponent)
function pruneLobby() {
  const now = Date.now();
  for (const [id, entry] of lobby) {
    if (entry.isBot) continue; // never prune bots
    if (now - entry.joinedAt > 60000) lobby.delete(id);
  }
}

// Instantly try to pair a player with anyone waiting in the lobby
function tryInstantPair(deviceId, username, socketId, isSpecialSession = false) {
  // Find any other real player waiting
  let paired = null;
  for (const [id, entry] of lobby) {
    if (id === deviceId) continue;
    paired = entry;
    break;
  }
  
  if (paired) {
    lobby.delete(paired.deviceId);
    lobby.delete(deviceId);
    
    const p1 = { deviceId: paired.deviceId, username: paired.username, socketId: paired.socketId };
    const p2 = { deviceId, username, socketId };
    const isBibleQuiz = isSpecialSession || paired.isSpecialSession;
    const match = createMatch(p1, p2, isBibleQuiz);
    
    const socket = io.sockets.sockets.get(socketId);
    if (socket) socket.join(match.matchId);
    const p1Socket = io.sockets.sockets.get(paired.socketId);
    if (p1Socket) p1Socket.join(match.matchId);
    
    const payload = (myDeviceId) => {
      const opp = Object.values(match.players).find(p => p.deviceId !== myDeviceId);
      return {
        matchId: match.matchId,
        seed: match.seed,
        questions: match.questions,
        opponent: { username: opp.username, deviceId: opp.deviceId },
      };
    };
    
    if (socket) socket.emit('match_found', payload(deviceId));
    if (p1Socket) p1Socket.emit('match_found', payload(paired.deviceId));
    console.log(`[instant-pair] ${match.matchId}  ${paired.username} vs ${username}`);
    
    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });
    broadcastToSpectators('match_update', {
      matchId: match.matchId,
      players: {
        [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: null },
        [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: null },
      },
    });
    broadcastLobbyCount();
    return true;
  }
  return false;
}

// ─── View / spectator helpers ─────────────────────────────────────────────────

function broadcastLobbyCount() {
  const count = lobby.size;
  io.emit('lobby_count', { count });
}

function broadcastToSpectators(event, data) {
  for (const sid of spectators) {
    const s = io.sockets.sockets.get(sid);
    if (s) s.emit(event, data);
  }
}

function getLeaderboardArray() {
  return [...leaderboard.values()].sort((a, b) => (b.wins || 0) - (a.wins || 0));
}

function broadcastLeaderboard() {
  const arr = getLeaderboardArray();
  broadcastToSpectators('leaderboard_update', arr);
  io.emit('leaderboard_update', arr);
}

function matchesToView() {
  const result = {};
  for (const [id, m] of matches) {
    result[id] = {
      matchId: m.matchId,
      players: Object.fromEntries(
        Object.entries(m.players).map(([did, p]) => [
          did,
          { username: p.username, deviceId: p.deviceId, answer: p.answer !== null ? '✓' : null },
        ])
      ),
    };
  }
  return result;
}

function sendViewState(socket) {
  socket.emit('view_state', {
    matches: matchesToView(),
    players: getLeaderboardArray(),
    lobbyCount: lobby.size,
  });
}

// ─── Match factory ────────────────────────────────────────────────────────────
function createMatch(p1, p2, isSpecialSession = false) {
  const matchId = 'match_' + Date.now() + '_' + Math.random().toString(36).slice(2, 6);
  const seed    = matchId;

  // Pick 5 questions from the right bank
  // Bible quiz (special session) uses Bible questions, normal matches use frontend seeded questions
  let bank = isSpecialSession && BIBLE_QUESTIONS.length > 0
    ? BIBLE_QUESTIONS
    : null;                 // normal: frontend picks from its own QUESTIONS_DB using the seed

  let questions = null;
  if (bank) {
    // Repeat pool if fewer than 5
    let pool = bank;
    while (pool.length < 5) pool = [...pool, ...bank];
    questions = seededShuffle(pool, seed).slice(0, 5);
  }
  // If bank is null, frontend uses getSeededQuestions(5, [], seed) — same seed = same questions

  const match = {
    matchId,
    seed,
    questions,          // null = use seeded frontend bank; array = use these exact questions
    players: {
      [p1.deviceId]: { ...p1, answer: null, answerTime: null, ready: false, connected: true },
      [p2.deviceId]: { ...p2, answer: null, answerTime: null, ready: false, connected: true },
    },
    questionIndex: 0,
    bothCorrectCount: 0,
    startTime: Date.now(),
    questionStartTime: Date.now(),
    active: true,
  };
  matches.set(matchId, match);
  return match;
}

// ─── Socket.io ────────────────────────────────────────────────────────────────
io.on('connection', (socket) => {
  console.log(`[+] connected  ${socket.id}`);

  // Clean up rate limit buckets on disconnect
  socket.on('disconnect', () => {
    const deviceId = socket.data.deviceId;
    console.log(`[-] disconnected ${socket.id} (${deviceId || 'unknown'})`);
    rateLimits.delete(socket.id);
    spectators.delete(socket.id);
    if (deviceId) {
      lobby.delete(deviceId);
      broadcastLobbyCount();
      // Mark player as disconnected in any active match
      for (const [matchId, match] of matches) {
        if (match.players[deviceId] && match.active) {
          match.players[deviceId].connected = false;
          match.players[deviceId].disconnectedAt = Date.now();
          socket.to(matchId).emit('opponent_disconnected', { matchId });
          // Give them 30s to reconnect before forfeiting
          setTimeout(() => {
            const m = matches.get(matchId);
            if (m && m.active && !m.players[deviceId]?.connected) {
              // Forfeit: opponent wins
              const winner = Object.values(m.players).find(p => p.deviceId !== deviceId);
              const loser  = match.players[deviceId];
              if (winner) {
                const winnerSocket = io.sockets.sockets.get(winner.socketId);
                if (winnerSocket) winnerSocket.emit('match_over_forfeit', { result: 'win', reason: 'Opponent left the match.' });
                // Update leaderboard
                const wb = leaderboard.get(winner.username) || { username: winner.username, wins: 0 };
                wb.wins = (wb.wins || 0) + 1;
                leaderboard.set(winner.username, wb);
                broadcastLeaderboard();
              }
              if (loser) {
                broadcastToSpectators('player_eliminated', { username: loser.username });
                broadcastToSpectators('match_ended', {
                  matchId,
                  winner: winner?.username,
                  loser: loser.username,
                });
              }
              m.active = false;
              matches.delete(matchId);
            }
          }, 30000);
        }
      }
    }
  });

  // ── Spectator / view-screen registration ────────────────────────────────
  socket.on('spectator_join', () => {
    spectators.add(socket.id);
    sendViewState(socket);
    console.log(`[spectator] ${socket.id} joined view`);
  });

  // ── Register device + session token ─────────────────────────────────────
  socket.on('register_device', ({ deviceId, sessionToken }) => {
    if (isRateLimited(socket.id, 'register_device', 3, 5000)) {
      return recordViolation(socket, 'Rate limit: register_device');
    }
    if (!deviceId || typeof deviceId !== 'string' || deviceId.length > 80) {
      return recordViolation(socket, 'Invalid deviceId');
    }

    // Session token check — block duplicate tabs/windows trying to play twice
    if (sessionToken) {
      const ok = validateSession(socket, sessionToken, deviceId);
      if (!ok) {
        socket.emit('security_duplicate_session', {
          message: 'Another session is already active for this device. Please close other tabs.',
        });
        return;
      }
    }

    socket.data.deviceId = deviceId;
    socket.data.sessionToken = sessionToken;
    devices.set(deviceId, socket.id);
  });

  // ── Player joins the matchmaking lobby ──────────────────────────────────
  socket.on('join_lobby', ({ deviceId, username, sessionToken, isSpecialSession }) => {
    if (isRateLimited(socket.id, 'join_lobby', 3, 10000)) {
      return recordViolation(socket, 'Rate limit: join_lobby');
    }
    if (!deviceId || !username || typeof username !== 'string') {
      return recordViolation(socket, 'Missing/invalid join_lobby fields');
    }
    if (username.length > 30) {
      return recordViolation(socket, 'Username too long');
    }

    socket.data.deviceId = deviceId;
    socket.data.username = username;
    socket.data.sessionToken = sessionToken;
    devices.set(deviceId, socket.id);

    // Session uniqueness check
    if (sessionToken) {
      const ok = validateSession(socket, sessionToken, deviceId);
      if (!ok) {
        socket.emit('security_duplicate_session', {
          message: 'Another session is already active. Only one active game per device is allowed.',
        });
        return;
      }
    }

    pruneLobby();

    // Tournament mode: only active when admin has set a scheduled date
    if (isRegistrationMode()) {
      // Registration is open — add player to waiting list
      registeredPlayers.set(deviceId, {
        username,
        deviceId,
        joinedAt: Date.now(),
        socketId: socket.id,
      });
      
      // Add to leaderboard as "waiting"
      if (!leaderboard.has(username)) {
        leaderboard.set(username, { username, wins: 0, stage: 'waiting' });
      }
      
      socket.emit('tournament_waiting', {
        message: 'You are registered! Waiting for tournament to start...',
        waitingCount: registeredPlayers.size,
        scheduledDate: tournamentConfig.scheduledDate,
      });
      
      // Broadcast to spectators
      broadcastToSpectators('player_joined', { username, waitingCount: registeredPlayers.size });
      io.emit('waiting_count', { count: registeredPlayers.size });
      
      console.log(`[tournament] ${username} registered (${registeredPlayers.size} waiting)`);
      return;
    }

    // Track in leaderboard
    if (!leaderboard.has(username)) {
      leaderboard.set(username, { username, wins: 0, stage: 'lobby' });
    }

    // Broadcast to view screens
    broadcastToSpectators('player_joined', { username, lobbyCount: lobby.size + 1 });
    broadcastLobbyCount();

    // Check if already in a match (reconnect scenario)
    for (const [matchId, match] of matches) {
      if (match.players[deviceId] && match.active) {
        // Reconnect — update socket reference
        match.players[deviceId].socketId = socket.id;
        match.players[deviceId].connected = true;
        socket.join(matchId);
        const opponent = Object.values(match.players).find(p => p.deviceId !== deviceId);
        socket.emit('match_rejoin', {
          matchId: match.matchId,
          seed: match.seed,
          questions: match.questions,
          questionIndex: match.questionIndex,
          opponent: { username: opponent?.username, deviceId: opponent?.deviceId },
        });
        // Notify opponent the player is back
        socket.to(matchId).emit('opponent_reconnected');
        console.log(`[reconnect] ${username} rejoined ${matchId}`);
        return;
      }
    }

    // Try to pair with someone already waiting
    let paired = null;
    for (const [waitingDeviceId, entry] of lobby) {
      if (waitingDeviceId !== deviceId) {
        paired = entry;
        lobby.delete(waitingDeviceId);
        break;
      }
    }

    if (paired) {
      // Bible quiz: wait until lobby has 10 players before pairing
      const isBibleQuiz = isSpecialSession || paired.isSpecialSession;
      if (isBibleQuiz && lobby.size + 1 < SPECIAL_LOBBY_REQUIRED) {
        // Not enough players yet — put current player in lobby too and wait
        lobby.set(deviceId, { socketId: socket.id, username, deviceId, joinedAt: Date.now(), isSpecialSession });
        // Put paired back too
        lobby.set(paired.deviceId, { socketId: paired.socketId, username: paired.username, deviceId: paired.deviceId, joinedAt: paired.joinedAt, isSpecialSession: paired.isSpecialSession });
        socket.emit('waiting_for_opponent');
        io.emit('lobby_count', { count: lobby.size });
        console.log(`[lobby bible] ${username} waiting — ${lobby.size}/${SPECIAL_LOBBY_REQUIRED} players`);
        return;
      }

      const p1 = { deviceId: paired.deviceId, username: paired.username, socketId: paired.socketId };
      const p2 = { deviceId, username, socketId: socket.id };
      const match = createMatch(p1, p2, isBibleQuiz);

      socket.join(match.matchId);
      const p1Socket = io.sockets.sockets.get(paired.socketId);
      if (p1Socket) p1Socket.join(match.matchId);

      const payload = (myDeviceId) => {
        const opp = Object.values(match.players).find(p => p.deviceId !== myDeviceId);
        return {
          matchId: match.matchId,
          seed: match.seed,
          questions: match.questions,
          opponent: { username: opp.username, deviceId: opp.deviceId },
        };
      };

      socket.emit('match_found', payload(deviceId));
      if (p1Socket) p1Socket.emit('match_found', payload(paired.deviceId));
      console.log(`[match] ${match.matchId}  ${paired.username} vs ${username}`);

      // Broadcast to view screens
      broadcastToSpectators('match_started', {
        matchId: match.matchId,
        p1: { username: p1.username, deviceId: p1.deviceId },
        p2: { username: p2.username, deviceId: p2.deviceId },
      });
      broadcastToSpectators('match_update', {
        matchId: match.matchId,
        players: {
          [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: null },
          [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: null },
        },
      });
      broadcastLobbyCount();
    } else {
      lobby.set(deviceId, { socketId: socket.id, username, deviceId, joinedAt: Date.now(), isSpecialSession });
      socket.emit('waiting_for_opponent');
      io.emit('lobby_count', { count: lobby.size });
      console.log(`[lobby] ${username} (${deviceId}) waiting…`);
    }
  });

  // ── Player submits answer ───────────────────────────────────────────────
  socket.on('submit_answer', ({ matchId, deviceId, answer, timeLeft, clientTimestamp }) => {
    if (isRateLimited(socket.id, 'submit_answer', 10, 15000)) {
      return recordViolation(socket, 'Rate limit: submit_answer');
    }

    const match = matches.get(matchId);
    if (!match || !match.active) return;

    const player = match.players[deviceId];
    if (!player || player.answer !== null) return; // already answered

    // Validate answer value
    const validOptions = [null, 'A', 'B', 'C', 'D'];
    if (!validOptions.includes(answer)) {
      return recordViolation(socket, `Invalid answer value: ${answer}`);
    }

    // Server-side timing check
    if (clientTimestamp && match.questionStartTime) {
      const elapsed = clientTimestamp - match.questionStartTime;
      if (elapsed < MIN_ANSWER_MS) {
        recordViolation(socket, `Answer too fast: ${elapsed}ms`);
        // Don't disconnect — just nullify the answer (treat as wrong)
        answer = null;
      }
    }

    player.answer    = answer;
    player.answerTime = Math.max(0, 9 - (timeLeft || 0));

    socket.to(matchId).emit('opponent_answered');

    const playerList = Object.values(match.players);
    if (playerList.every(p => p.answer !== null)) evaluateRound(match, io);
  });

  // ── Timeout: player didn't answer in time ─────────────────────────────
  socket.on('answer_timeout', ({ matchId, deviceId }) => {
    if (isRateLimited(socket.id, 'answer_timeout', 10, 15000)) return;
    const match = matches.get(matchId);
    if (!match || !match.active) return;
    const player = match.players[deviceId];
    if (!player || player.answer !== null) return;
    player.answer = null;
    player.answerTime = 9;

    const playerList = Object.values(match.players);
    if (playerList.every(p => p.answer !== null)) evaluateRound(match, io);
  });

  // ── Back-navigation / visibility violation report ─────────────────────
  socket.on('report_violation', ({ matchId, type }) => {
    const deviceId = socket.data.deviceId;
    console.warn(`[⚠️  CLIENT VIOLATION] ${deviceId} — ${type} in match ${matchId}`);
    recordViolation(socket, `client_report: ${type}`);
  });

  // ── Admin: push special session ────────────────────────────────────────
  socket.on('admin_set_special_session', (ss) => {
    specialSession = ss;
    io.emit('special_session_updated', ss);
    console.log(`[admin] special session ${ss.active ? 'ACTIVATED' : 'deactivated'} (${ss.questions?.length || 0} questions)`);
  });
});

// ─── Round evaluation (server-authoritative) ──────────────────────────────────
function evaluateRound(match, io) {
  const [p1, p2] = Object.values(match.players);

  // Determine which question we're on
  const qIndex  = match.questionIndex;
  const question = match.questions ? match.questions[qIndex] : null;

  // If questions are from the frontend bank (question === null), we rely on
  // the frontend to evaluate — server just relays both answers
  if (!question) {
    // Relay both answers — use room broadcast but real socket for bots scenario
    const roundAnswersPayload = {
      questionIndex: qIndex,
      answers: {
        [p1.deviceId]: p1.answer,
        [p2.deviceId]: p2.answer,
      },
    };
    // Send to real players only (bots have no socket)
    [p1, p2].forEach(p => {
      if (!p.isBot) {
        const sock = io.sockets.sockets.get(p.socketId);
        if (sock) sock.emit('round_answers', roundAnswersPayload);
      }
    });
    // Broadcast to view screens
    broadcastToSpectators('match_update', {
      matchId: match.matchId,
      players: {
        [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: p1.answer ? '✓' : null },
        [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: p2.answer ? '✓' : null },
      },
    });
    // Reset for next question
    p1.answer = null; p1.answerTime = null;
    p2.answer = null; p2.answerTime = null;
    match.questionIndex++;
    return;
  }

  // Server-authoritative evaluation
  const p1Correct = p1.answer === question.correct;
  const p2Correct = p2.answer === question.correct;

  let p1Result, p2Result, matchOver = false;

  if (p1Correct && p2Correct) {
    match.bothCorrectCount = (match.bothCorrectCount || 0) + 1;
    if (match.bothCorrectCount >= 3 || match.questionIndex >= (match.questions.length - 1)) {
      // Speed tiebreak — faster answer wins
      p1Result = p1.answerTime <= p2.answerTime ? 'win' : 'lose';
      p2Result = p1Result === 'win' ? 'lose' : 'win';
      matchOver = true;
    } else {
      p1Result = 'next';
      p2Result = 'next';
      match.questionIndex++;
      match.questionStartTime = Date.now(); // reset timing for next question
    }
  } else if (p1Correct) {
    p1Result = 'win'; p2Result = 'lose'; matchOver = true;
  } else if (p2Correct) {
    p1Result = 'lose'; p2Result = 'win'; matchOver = true;
  } else {
    // Both wrong
    p1Result = 'gameover'; p2Result = 'gameover'; matchOver = true;
  }

  // Emit result to each player
  const emit = (player, result) => {
    const sock = io.sockets.sockets.get(player.socketId);
    if (sock) {
      sock.emit('round_result', {
        result,
        questionIndex: qIndex,
        correctAnswer: question.correct,
        myAnswer: player.answer,
        opponentAnswer: Object.values(match.players).find(p => p.deviceId !== player.deviceId).answer,
        matchOver,
      });
    }
  };
  emit(p1, p1Result);
  emit(p2, p2Result);

  // Broadcast answer progress to view screens (anonymised)
  broadcastToSpectators('match_update', {
    matchId: match.matchId,
    players: {
      [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: p1.answer ? '✓' : null },
      [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: p2.answer ? '✓' : null },
    },
  });

  // If both answered correctly, notify view screen for merge animation
  if (p1Correct && p2Correct && !matchOver) {
    broadcastToSpectators('both_correct', {
      matchId: match.matchId,
      p1: p1.username,
      p2: p2.username,
    });
  }

  if (matchOver) {
    const winner = p1Result === 'win' ? p1 : p2Result === 'win' ? p2 : null;
    const loser  = p1Result === 'lose' ? p1 : p2Result === 'lose' ? p2 : null;

    // Update leaderboard
    if (winner) {
      const wb = leaderboard.get(winner.username) || { username: winner.username, wins: 0, totalTime: 0 };
      wb.wins = (wb.wins || 0) + 1;
      // totalTime: sum of answerTimes for this match winner
      const winnerAnswerTime = winner.answerTime || 0;
      wb.totalTime = (wb.totalTime || 0) + winnerAnswerTime;
      leaderboard.set(winner.username, wb);
      broadcastLeaderboard();
    }

    // Broadcast elimination + match-ended to view screens
    if (loser) {
      broadcastToSpectators('player_eliminated', { username: loser.username });
    }
    broadcastToSpectators('match_ended', {
      matchId: match.matchId,
      winner: winner?.username ?? null,
      loser:  loser?.username ?? null,
    });

    match.active = false;
    setTimeout(() => matches.delete(match.matchId), 120000); // clean up after 2min
  } else {
    // Reset answers for next question
    p1.answer = null; p1.answerTime = null;
    p2.answer = null; p2.answerTime = null;
  }
}

// ─── MongoDB connection ───────────────────────────────────────────────────────
mongoose
  .connect(process.env.MONGO_URI)
  .then(() => console.log('✅ Connected to MongoDB'))
  .catch((err) => console.error('❌ MongoDB connection error:', err));

// ─── User registration (save username + deviceId) ─────────────────────────────
app.post('/api/users', async (req, res) => {
  try {
    const { username, deviceId } = req.body;

    if (!username || !deviceId) {
      return res.status(400).json({ error: 'username and deviceId are required' });
    }
    if (typeof username !== 'string' || username.length > 30) {
      return res.status(400).json({ error: 'Invalid username (max 30 chars)' });
    }

    // Upsert: update username if deviceId already exists, otherwise create
    const user = await User.findOneAndUpdate(
      { deviceId },
      { username, deviceId },
      { upsert: true, new: true, runValidators: true }
    );

    res.status(201).json({ ok: true, user });
  } catch (err) {
    console.error('[api/users] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get user by deviceId
app.get('/api/users/:deviceId', async (req, res) => {
  try {
    const user = await User.findOne({ deviceId: req.params.deviceId });
    if (!user) return res.status(404).json({ error: 'User not found' });
    res.json(user);
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// ─── Admin login ──────────────────────────────────────────────────────────────
app.post('/admin/login', async (req, res) => {
  try {
    const { email, password } = req.body;

    if (!email || !password) {
      return res.status(400).json({ error: 'email and password are required' });
    }

    const admin = await Admin.findOne({ email });
    if (!admin) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }

    const isMatch = await admin.comparePassword(password);
    if (!isMatch) {
      return res.status(401).json({ error: 'Invalid credentials' });
    }

    const token = jwt.sign(
      { adminId: admin._id, email: admin.email },
      process.env.JWT_SECRET,
      { expiresIn: '24h' }
    );

    res.json({ ok: true, token, admin: { id: admin._id, email: admin.email } });
  } catch (err) {
    console.error('[admin/login] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// ─── Admin auth middleware ────────────────────────────────────────────────────
function requireAdmin(req, res, next) {
  const authHeader = req.headers.authorization;
  if (!authHeader || !authHeader.startsWith('Bearer ')) {
    return res.status(401).json({ error: 'No token provided' });
  }
  try {
    const token = authHeader.split(' ')[1];
    const decoded = jwt.verify(token, process.env.JWT_SECRET);
    req.admin = decoded;
    next();
  } catch {
    return res.status(401).json({ error: 'Invalid or expired token' });
  }
}

// ─── Admin REST endpoint to push special session ──────────────────────────────
app.post('/admin/special-session', (req, res) => {
  specialSession = req.body;
  io.emit('special_session_updated', specialSession);
  broadcastToSpectators('special_session_updated', specialSession);
  res.json({ ok: true });
});
app.get('/admin/special-session', (_, res) => res.json(specialSession));

// ─── Leaderboard REST endpoint ────────────────────────────────────────────────
app.get('/leaderboard', (_, res) => res.json(getLeaderboardArray()));

// ─── Tournament REST endpoints ───────────────────────────────────────────────
// Get tournament status (public)
app.get('/tournament/status', (_, res) => {
  res.json({
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    registrationOpen: isRegistrationMode(),
    registeredCount: registeredPlayers.size,
    players: [...registeredPlayers.values()].map(p => ({ username: p.username, joinedAt: p.joinedAt })),
  });
});

// Admin: Schedule a tournament (sets date → opens registration)
app.post('/admin/tournament/schedule', (req, res) => {
  const { scheduledDate } = req.body;
  if (!scheduledDate) {
    return res.status(400).json({ error: 'scheduledDate is required (ISO string)' });
  }
  
  tournamentConfig.scheduledDate = scheduledDate;
  tournamentConfig.tournamentStarted = false;
  registeredPlayers.clear();
  
  // Schedule auto-start timer
  scheduleAutoStart(scheduledDate);
  
  io.emit('tournament_config_updated', {
    scheduledDate: tournamentConfig.scheduledDate,
    registrationOpen: true,
    tournamentStarted: false,
  });
  
  console.log(`[tournament] Scheduled for ${scheduledDate} — registration open`);
  res.json({ ok: true, scheduledDate, message: 'Registration is now open!' });
});

// Admin: Get all registered players
app.get('/admin/tournament/players', (_, res) => {
  res.json({
    players: [...registeredPlayers.values()],
    count: registeredPlayers.size,
    config: tournamentConfig,
  });
});

// Admin: Start the tournament (begin pairing)
app.post('/admin/tournament/start', (req, res) => {
  if (!tournamentConfig.scheduledDate) {
    return res.status(400).json({ error: 'No tournament scheduled. Set a date first.' });
  }

  // Clear auto-start timer since admin is starting manually
  if (autoStartTimer) {
    clearTimeout(autoStartTimer);
    autoStartTimer = null;
  }

  const result = startTournament();
  if (result.error) {
    return res.status(400).json(result);
  }
  res.json(result);
});

// Check if device has already joined special session
app.get('/api/check-joined/:deviceId', (req, res) => {
  const { deviceId } = req.params;
  const hasJoined = registeredPlayers.has(deviceId);
  const playerInfo = registeredPlayers.get(deviceId);
  res.json({ 
    hasJoined,
    username: playerInfo?.username || null,
    joinedAt: playerInfo?.joinedAt || null
  });
});

// Admin: Reset tournament (clear schedule + all registrations → back to normal mode)
app.post('/admin/tournament/reset', (req, res) => {
  registeredPlayers.clear();
  tournamentConfig.scheduledDate = null;
  tournamentConfig.tournamentStarted = false;
  lobby.clear();
  
  io.emit('tournament_reset', { message: 'Tournament has been reset' });
  console.log('[tournament] Reset — back to normal mode');
  res.json({ ok: true });
});

// Admin: Full reset — clears ALL data (tournament, matches, leaderboard, lobby)
app.post('/admin/reset-all', (req, res) => {
  // Clear tournament
  registeredPlayers.clear();
  tournamentConfig.scheduledDate = null;
  tournamentConfig.tournamentStarted = false;
  
  // Clear matches & lobby
  lobby.clear();
  matches.clear();
  
  // Clear leaderboard
  leaderboard.clear();
  
  // Clear device tracking
  devices.clear();
  sessions.clear();
  violations.clear();
  rateLimits.clear();
  
  // Notify all clients
  io.emit('tournament_reset', { message: 'Game has been fully reset' });
  io.emit('force_reload', { message: 'Admin reset the game' });
  
  console.log('[admin] FULL RESET — all data cleared');
  res.json({ ok: true, message: 'All data cleared' });
});
const DEMO_NAMES = [
  'AkintundeB','FunmilatoA','KayodeM','BisiO','TundeF',
  'AdaobiC','EmekaN','NgoziU','YemiA','TopeS',
  'LaraB','IfeoluwaK','SeunO','RotimiA','DamiR',
  'BisodunM','FeranmiT','GbengaJ','KemiL','OluwaseunP',
];

// Active demo bots: deviceId → { username, deviceId, wins, totalTime }
const demoBots = new Map();
let demoEnabled = false;
let demoPairInterval = null;

// Make a bot "join" the lobby and immediately be available for pairing
function addBotToLobby(name, idx) {
  const deviceId = `demo_bot_${idx}`;
  if (lobby.has(deviceId)) return; // already waiting
  const fakeSocketId = `bot_socket_${idx}_${Date.now()}`;
  lobby.set(deviceId, {
    socketId: fakeSocketId,
    username: name,
    deviceId,
    joinedAt: Date.now(),
    isBot: true,
  });
  if (!leaderboard.has(name)) {
    leaderboard.set(name, { username: name, wins: 0, totalTime: 0, stage: 'playing' });
  }
  if (!demoBots.has(deviceId)) {
    demoBots.set(deviceId, { username: name, deviceId, wins: 0, totalTime: 0 });
  }
}

// When a bot is in a match, simulate it answering after a short random delay
function simulateBotAnswer(match, botDeviceId) {
  const bot = match.players[botDeviceId];
  if (!bot) return;
  // Bot answers after 1–5 seconds, gets it right ~55% of the time
  const delay = 1000 + Math.floor(Math.random() * 4000);
  setTimeout(() => {
    const m = matches.get(match.matchId);
    if (!m || !m.active) return;
    if (m.players[botDeviceId].answer !== null) return; // already answered

    const options = ['A','B','C','D'];
    const question = m.questions ? m.questions[m.questionIndex] : null;
    let answer;
    if (question) {
      answer = Math.random() < 0.55 ? question.correct : options.filter(o => o !== question.correct)[Math.floor(Math.random() * 3)];
    } else {
      answer = options[Math.floor(Math.random() * 4)];
    }
    const answerTime = Math.round(delay / 1000);
    m.players[botDeviceId].answer = answer;
    m.players[botDeviceId].answerTime = answerTime;

    // Notify the real opponent that bot has answered
    const opponent = Object.values(m.players).find(p => p.deviceId !== botDeviceId);
    if (opponent && opponent.socketId) {
      const oppSocket = io.sockets.sockets.get(opponent.socketId);
      if (oppSocket) oppSocket.emit('opponent_answered');
    }

    // If both answered, evaluate
    if (Object.values(m.players).every(p => p.answer !== null)) {
      evaluateRound(m, io);
    }
  }, delay);
}

// After evaluateRound, if the bot won, put it back in the lobby after a short pause
function reQueueBot(botDeviceId) {
  const bot = demoBots.get(botDeviceId);
  if (!bot || !demoEnabled) return;
  setTimeout(() => {
    if (!demoEnabled) return;
    const idx = [...demoBots.keys()].indexOf(botDeviceId);
    addBotToLobby(bot.username, idx);
    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });
    broadcastToSpectators('lobby_count', { count: lobby.size });
    // Try to pair with any waiting real player
    tryPairBotsWithWaiting();
  }, 2000 + Math.random() * 3000);
}

// Scan the lobby: pair bots with real players
function tryPairBotsWithWaiting() {
  const realPlayers = [];
  const botPlayers  = [];
  for (const [did, entry] of lobby) {
    if (entry.isBot) botPlayers.push(entry);
    else realPlayers.push(entry);
  }
  // Pair each real player with a bot
  for (const real of realPlayers) {
    if (botPlayers.length === 0) break;
    const bot = botPlayers.shift();
    lobby.delete(real.deviceId);
    lobby.delete(bot.deviceId);

    const p1 = { deviceId: real.deviceId, username: real.username, socketId: real.socketId };
    const p2 = { deviceId: bot.deviceId,  username: bot.username,  socketId: bot.socketId };
    const match = createMatch(p1, p2);

    // Notify real player
    const realSocket = io.sockets.sockets.get(real.socketId);
    if (realSocket) {
      realSocket.join(match.matchId);
      realSocket.emit('match_found', {
        matchId: match.matchId,
        seed: match.seed,
        questions: match.questions,
        opponent: { username: bot.username, deviceId: bot.deviceId },
      });
    }

    console.log(`[demo] bot ${bot.username} paired with ${real.username}`);

    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });

    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });
    broadcastToSpectators('lobby_count', { count: lobby.size });

    // Bot starts answering questions
    simulateBotAnswer(match, bot.deviceId);
  }

  // Also pair bots with each other for visual activity on view screen
  while (botPlayers.length >= 2) {
    const b1 = botPlayers.shift();
    const b2 = botPlayers.shift();
    lobby.delete(b1.deviceId);
    lobby.delete(b2.deviceId);

    const match = createMatch(
      { deviceId: b1.deviceId, username: b1.username, socketId: b1.socketId },
      { deviceId: b2.deviceId, username: b2.username, socketId: b2.socketId }
    );

    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: b1.username, deviceId: b1.deviceId },
      p2: { username: b2.username, deviceId: b2.deviceId },
    });

    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });

    simulateBotAnswer(match, b1.deviceId);
    simulateBotAnswer(match, b2.deviceId);
  }
}

app.post('/admin/demo/start', (req, res) => {
  const count = Math.min(Math.max(parseInt(req.body.count) || 10, 2), 20);
  demoEnabled = true;

  // Add bots to lobby
  for (let i = 0; i < count; i++) {
    addBotToLobby(DEMO_NAMES[i % DEMO_NAMES.length], i);
  }

  broadcastLeaderboard();
  broadcastLobbyCount();
  io.emit('lobby_count', { count: lobby.size });
  broadcastToSpectators('lobby_count', { count: lobby.size });

  // Pair bots among themselves immediately for view screen activity
  tryPairBotsWithWaiting();

  // Keep lobby topped up: every 5s, if demo is on, add bots back up to count
  if (demoPairInterval) clearInterval(demoPairInterval);
  demoPairInterval = setInterval(() => {
    if (!demoEnabled) { clearInterval(demoPairInterval); return; }
    let inLobby = 0;
    for (const [, e] of lobby) if (e.isBot) inLobby++;
    const need = Math.max(0, 2 - inLobby); // keep at least 2 bots in lobby
    for (let i = 0; i < need; i++) {
      const idx = Math.floor(Math.random() * count);
      addBotToLobby(DEMO_NAMES[idx % DEMO_NAMES.length], idx);
    }
    if (need > 0) {
      tryPairBotsWithWaiting();
      broadcastLobbyCount();
      io.emit('lobby_count', { count: lobby.size });
    }
  }, 5000);

  res.json({ ok: true, count });
});

app.post('/admin/demo/stop', (req, res) => {
  demoEnabled = false;
  if (demoPairInterval) { clearInterval(demoPairInterval); demoPairInterval = null; }

  // Remove all bots from lobby
  for (const [did] of demoBots) lobby.delete(did);
  demoBots.clear();

  broadcastLobbyCount();
  io.emit('lobby_count', { count: lobby.size });
  broadcastToSpectators('lobby_count', { count: lobby.size });
  broadcastLeaderboard();
  res.json({ ok: true });
});

// ─── Start ────────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 4000;
server.listen(PORT, () => console.log(`\n🚀 QuizDuel server listening on http://localhost:${PORT}\n`));
