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
const User              = require('./models/User');
const TournamentPlayer  = require('./models/TournamentPlayer');
const TournamentSchedule = require('./models/TournamentSchedule');

// ─── Hardcoded admin credentials ─────────────────────────────────────────────
const ADMIN_EMAIL    = 'indtropical@gmail.com';
const ADMIN_PASSWORD = 'Olatun@900';

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

// ─── NEW: Dedicated Queues for Real-Time Matchmaking ─────────────────────────
// waitingQueue: players waiting to be matched for the FIRST time in a round
// winnersQueue: players who WON their match, waiting to be paired with another winner
// Key: deviceId → { deviceId, username, socketId, round, queuedAt, wins }
const waitingQueue = new Map();
const winnersQueue = new Map();

// Matchmaking lock to prevent race conditions
let matchmakingLock = false;

// Track which players are currently IN an active match (prevents double-queueing)
const playersInMatch = new Set(); // deviceIds of players currently in a match

// Server-driven match timers: matchId → { timer, currentQuestion, questionStartTime }
const matchTimers = new Map();

// ─── Tournament Registration System ──────────────────────────────────────────
// Players enter username before tournament, wait until admin starts, then all play
const registeredPlayers = new Map(); // deviceId → { username, deviceId, joinedAt, socketId }
let tournamentConfig = {
  scheduledDate: null,            // ISO string — when set, registration mode is active
  tournamentStarted: false,       // Has the admin started the tournament?
};

// Elimination bracket: tracks winners waiting for next round pairing
// round → [ { deviceId, username, socketId, wins } ]
const bracketWinners = new Map();
let currentRound = 1;

// Registration mode is ON only when admin has set a scheduled date
function isRegistrationMode() {
  return tournamentConfig.scheduledDate !== null && !tournamentConfig.tournamentStarted;
}

function canStartPlaying() {
  return tournamentConfig.tournamentStarted;
}

// Get count of currently connected (active) players
function getActivePlayerCount() {
  let count = 0;
  for (const player of registeredPlayers.values()) {
    if (player.socketId) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) count++;
    }
  }
  return count;
}

// Get list of currently connected players
function getActivePlayers() {
  const active = [];
  for (const player of registeredPlayers.values()) {
    if (player.socketId) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) {
        active.push(player);
      }
    }
  }
  return active;
}

// Auto-start timer reference
let autoStartTimer = null;

// ─── Elimination bracket helpers ─────────────────────────────────────────────

// Shuffle array in-place (Fisher-Yates)
function shuffleArray(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

// Pair a list of players into Bible quiz matches for the current round.
// Returns the list of match descriptors created.
function pairPlayersForRound(players, round, questionsPerMatch = 5) {
  shuffleArray(players);
  const matchPairs = [];

  for (let i = 0; i < players.length - 1; i += 2) {
    const p1 = players[i];
    const p2 = players[i + 1];

    // ATOMIC: Check they're not already in a match
    if (playersInMatch.has(p1.deviceId) || playersInMatch.has(p2.deviceId)) {
      console.log(`[pairPlayersForRound] Skipping already-in-match players: ${p1.username} or ${p2.username}`);
      continue;
    }

    // Mark as in match BEFORE creating
    playersInMatch.add(p1.deviceId);
    playersInMatch.add(p2.deviceId);

    // Remove from any queues
    waitingQueue.delete(p1.deviceId);
    waitingQueue.delete(p2.deviceId);
    winnersQueue.delete(p1.deviceId);
    winnersQueue.delete(p2.deviceId);

    const match = createMatch(
      { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
      { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
      true, // always Bible quiz for tournament
      questionsPerMatch
    );
    // Tag the match with round info so evaluateRound can trigger next-round logic
    match.tournamentRound = round;

    matchPairs.push({
      matchId: match.matchId,
      round,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });

    const s1 = io.sockets.sockets.get(p1.socketId);
    const s2 = io.sockets.sockets.get(p2.socketId);
    
    // Build match payload for each player - include their own info AND opponent info
    const basePayload = { 
      matchId: match.matchId, 
      matchSeed: match.seed, 
      questions: match.questions,
      round,
      totalQuestions: match.questions?.length || questionsPerMatch,
      isTournament: true,
    };

    if (s1) { 
      s1.join(match.matchId); 
      s1.emit('match_found', { 
        ...basePayload, 
        you: { username: p1.username, deviceId: p1.deviceId },
        opponent: { username: p2.username, deviceId: p2.deviceId } 
      }); 
    }
    if (s2) { 
      s2.join(match.matchId); 
      s2.emit('match_found', { 
        ...basePayload, 
        you: { username: p2.username, deviceId: p2.deviceId },
        opponent: { username: p1.username, deviceId: p1.deviceId } 
      }); 
    }

    // Start server-driven timer for the match
    startMatchTimer(match);

    console.log(`[tournament R${round}] Paired: ${p1.username} vs ${p2.username} → ${match.matchId} (${questionsPerMatch} questions)`);
  }

  // Odd player out → automatic bye (advances to next round)
  if (players.length % 2 !== 0) {
    const byePlayer = players[players.length - 1];
    const s = io.sockets.sockets.get(byePlayer.socketId);
    if (s) s.emit('tournament_bye', { message: 'You got a bye this round! You advance automatically.', username: byePlayer.username, round });

    // Immediately queue bye player as a winner for the next round
    queueWinnerForNextRound(byePlayer, round);
    console.log(`[tournament R${round}] Bye: ${byePlayer.username}`);
  }

  broadcastToSpectators('round_started', { round, matchCount: matchPairs.length });
  io.emit('tournament_round_started', { round, matchCount: matchPairs.length, playerCount: players.length });
  return matchPairs;
}

// Called after a match ends: queue winner into next round bracket
function queueWinnerForNextRound(player, round) {
  if (!bracketWinners.has(round)) bracketWinners.set(round, []);
  bracketWinners.get(round).push(player);

  // ALSO add to winnersQueue for instant re-matching
  if (!winnersQueue.has(player.deviceId) && !playersInMatch.has(player.deviceId)) {
    winnersQueue.set(player.deviceId, {
      deviceId: player.deviceId,
      username: player.username,
      socketId: player.socketId,
      round: round + 1,
      queuedAt: Date.now(),
      wins: player.wins || 1,
    });
    console.log(`[winnersQueue] ${player.username} added (${winnersQueue.size} waiting)`);
  }

  const waitingWinners = bracketWinners.get(round);
  console.log(`[bracket R${round}] ${player.username} queued (${waitingWinners.length} waiting)`);

  // TRY INSTANT WINNER PAIRING: if we have 2+ winners, pair them immediately
  tryPairWinners(round);
}

// Advance all waiting winners into the next round
function advanceToNextRound(completedRound) {
  const nextRound = completedRound + 1;
  currentRound = nextRound;

  const advancingPlayers = bracketWinners.get(completedRound) || [];
  bracketWinners.delete(completedRound);

  // Filter to only include still-connected players
  const connectedAdvancers = advancingPlayers.filter(p => {
    if (!p.socketId) return false;
    const socket = io.sockets.sockets.get(p.socketId);
    return socket && socket.connected;
  });

  console.log(`[tournament] Round ${completedRound} complete — ${advancingPlayers.length} winners, ${connectedAdvancers.length} still connected`);

  if (connectedAdvancers.length === 0) {
    console.log(`[tournament] No connected players remain — tournament ends`);
    io.emit('tournament_ended', { reason: 'All remaining players disconnected' });
    return;
  }

  if (connectedAdvancers.length === 1) {
    declareTournamentChampion(connectedAdvancers[0]);
    return;
  }

  // Calculate questions per match based on remaining player count
  const questionsPerMatch = getQuestionsPerMatch(connectedAdvancers.length);
  console.log(`[tournament] Round ${nextRound}: Using ${questionsPerMatch} questions per match for ${connectedAdvancers.length} players`);

  io.emit('tournament_next_round', { round: nextRound, playerCount: connectedAdvancers.length, questionsPerMatch });
  pairPlayersForRound(connectedAdvancers, nextRound, questionsPerMatch);
}

// NEW: Try to pair winners INSTANTLY when they become available
function tryPairWinners(completedRound) {
  if (matchmakingLock) {
    console.log(`[tryPairWinners] Matchmaking locked, will retry shortly`);
    setTimeout(() => tryPairWinners(completedRound), 100);
    return;
  }

  matchmakingLock = true;
  const nextRound = completedRound + 1;

  try {
    // Get all connected winners from the winnersQueue
    const availableWinners = [];
    for (const [deviceId, player] of winnersQueue) {
      // Skip if player is already in a match
      if (playersInMatch.has(deviceId)) {
        winnersQueue.delete(deviceId);
        continue;
      }
      // Verify socket is still connected
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) {
        availableWinners.push(player);
      } else {
        // Ghost user — remove from queue
        winnersQueue.delete(deviceId);
        console.log(`[winnersQueue] Removed ghost: ${player.username}`);
      }
    }

    console.log(`[tryPairWinners] ${availableWinners.length} winners available for pairing`);

    // Pair winners in pairs of 2
    while (availableWinners.length >= 2) {
      const p1 = availableWinners.shift();
      const p2 = availableWinners.shift();

      // Remove from winnersQueue ATOMICALLY
      winnersQueue.delete(p1.deviceId);
      winnersQueue.delete(p2.deviceId);

      // Also remove from bracketWinners to prevent double-processing
      const bracket = bracketWinners.get(completedRound) || [];
      const filteredBracket = bracket.filter(p => p.deviceId !== p1.deviceId && p.deviceId !== p2.deviceId);
      if (filteredBracket.length > 0) {
        bracketWinners.set(completedRound, filteredBracket);
      } else {
        bracketWinners.delete(completedRound);
      }

      // Mark as in match
      playersInMatch.add(p1.deviceId);
      playersInMatch.add(p2.deviceId);

      // Calculate questions
      const questionsPerMatch = getQuestionsPerMatch(winnersQueue.size + availableWinners.length + 2);

      // Create match
      const match = createMatch(
        { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
        { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
        true, // Bible quiz for tournament
        questionsPerMatch
      );
      match.tournamentRound = nextRound;

      // Emit to players
      const basePayload = {
        matchId: match.matchId,
        matchSeed: match.seed,
        questions: match.questions,
        round: nextRound,
        totalQuestions: match.questions?.length || questionsPerMatch,
        isTournament: true,
      };

      const s1 = io.sockets.sockets.get(p1.socketId);
      const s2 = io.sockets.sockets.get(p2.socketId);

      if (s1) {
        s1.join(match.matchId);
        s1.emit('match_found', {
          ...basePayload,
          you: { username: p1.username, deviceId: p1.deviceId },
          opponent: { username: p2.username, deviceId: p2.deviceId },
        });
      }
      if (s2) {
        s2.join(match.matchId);
        s2.emit('match_found', {
          ...basePayload,
          you: { username: p2.username, deviceId: p2.deviceId },
          opponent: { username: p1.username, deviceId: p1.deviceId },
        });
      }

      // Start server-driven timer for the match
      startMatchTimer(match);

      console.log(`[instant-winner-pair] R${nextRound}: ${p1.username} vs ${p2.username} → ${match.matchId}`);
      broadcastToSpectators('match_started', {
        matchId: match.matchId,
        round: nextRound,
        p1: { username: p1.username, deviceId: p1.deviceId },
        p2: { username: p2.username, deviceId: p2.deviceId },
      });
    }

    // Check if only 1 winner remains and no active matches
    if (availableWinners.length === 1) {
      const activeMatches = [...matches.values()].filter(m => m.tournamentRound && m.active);
      if (activeMatches.length === 0) {
        // This is the champion!
        const champion = availableWinners[0];
        winnersQueue.delete(champion.deviceId);
        declareTournamentChampion(champion);
      } else {
        // Wait for other matches to complete
        console.log(`[tryPairWinners] 1 winner waiting, ${activeMatches.length} matches still active`);
      }
    }
  } finally {
    matchmakingLock = false;
  }
}

// NEW: Server-driven match timer
function startMatchTimer(match) {
  const QUESTION_TIME_MS = 10000; // 10 seconds per question
  const COUNTDOWN_INTERVAL_MS = 1000; // emit countdown every second

  let timeLeft = 10;
  match.questionStartTime = Date.now();

  const countdownInterval = setInterval(() => {
    timeLeft--;
    
    // Emit countdown to both players
    io.to(match.matchId).emit('timer_tick', {
      matchId: match.matchId,
      timeLeft,
      questionIndex: match.questionIndex,
    });

    if (timeLeft <= 0) {
      clearInterval(countdownInterval);
      
      // Force timeout for any player who hasn't answered
      const players = Object.values(match.players);
      let needsEval = false;
      
      for (const player of players) {
        if (player.answer === null && match.active) {
          player.answer = null; // explicit timeout
          player.answerTime = 10;
          needsEval = true;
        }
      }

      // Evaluate if both have now answered (either by submission or timeout)
      if (needsEval && players.every(p => p.answer !== null || p.answerTime === 10)) {
        // Set answer to null for timed out players
        players.forEach(p => {
          if (p.answer === null) p.answerTime = 10;
        });
        evaluateRound(match, io);
      }
    }
  }, COUNTDOWN_INTERVAL_MS);

  // Store timer reference for cleanup
  matchTimers.set(match.matchId, {
    interval: countdownInterval,
    currentQuestion: match.questionIndex,
    questionStartTime: match.questionStartTime,
  });
}

// Clean up timer when match ends
function cleanupMatchTimer(matchId) {
  const timerData = matchTimers.get(matchId);
  if (timerData) {
    clearInterval(timerData.interval);
    matchTimers.delete(matchId);
  }
}

// NEW: Try to instantly pair players from the waitingQueue
function tryInstantQueuePair() {
  if (matchmakingLock) {
    setTimeout(tryInstantQueuePair, 50);
    return;
  }

  matchmakingLock = true;
  
  try {
    // Get connected players from waiting queue
    const availablePlayers = [];
    for (const [deviceId, player] of waitingQueue) {
      // Skip if already in match
      if (playersInMatch.has(deviceId)) {
        waitingQueue.delete(deviceId);
        continue;
      }
      
      // Verify socket is connected
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) {
        availablePlayers.push(player);
      } else {
        // Ghost user — remove
        waitingQueue.delete(deviceId);
        console.log(`[waitingQueue] Removed ghost: ${player.username}`);
      }
    }
    
    console.log(`[tryInstantQueuePair] ${availablePlayers.length} players available`);
    
    // Pair in groups of 2
    while (availablePlayers.length >= 2) {
      const p1 = availablePlayers.shift();
      const p2 = availablePlayers.shift();
      
      // Remove from queue ATOMICALLY
      waitingQueue.delete(p1.deviceId);
      waitingQueue.delete(p2.deviceId);
      
      // Mark as in match
      playersInMatch.add(p1.deviceId);
      playersInMatch.add(p2.deviceId);
      
      // Create match
      const questionsPerMatch = 5;
      const match = createMatch(
        { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
        { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
        true, // Bible quiz
        questionsPerMatch
      );
      match.tournamentRound = 1; // Default to round 1 for queue matches
      
      const basePayload = {
        matchId: match.matchId,
        matchSeed: match.seed,
        questions: match.questions,
        round: 1,
        totalQuestions: questionsPerMatch,
        isTournament: true,
      };
      
      const s1 = io.sockets.sockets.get(p1.socketId);
      const s2 = io.sockets.sockets.get(p2.socketId);
      
      if (s1) {
        s1.join(match.matchId);
        s1.emit('match_found', {
          ...basePayload,
          you: { username: p1.username, deviceId: p1.deviceId },
          opponent: { username: p2.username, deviceId: p2.deviceId },
        });
      }
      if (s2) {
        s2.join(match.matchId);
        s2.emit('match_found', {
          ...basePayload,
          you: { username: p2.username, deviceId: p2.deviceId },
          opponent: { username: p1.username, deviceId: p1.deviceId },
        });
      }
      
      // Start server-driven timer
      startMatchTimer(match);
      
      console.log(`[instant-queue-pair] ${p1.username} vs ${p2.username} → ${match.matchId}`);
      broadcastToSpectators('match_started', {
        matchId: match.matchId,
        p1: { username: p1.username, deviceId: p1.deviceId },
        p2: { username: p2.username, deviceId: p2.deviceId },
      });
    }
    
    // Notify remaining players of their queue position
    let position = 1;
    for (const [, player] of waitingQueue) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket) {
        socket.emit('queue_update', { 
          position, 
          totalWaiting: waitingQueue.size,
          message: `Position ${position} of ${waitingQueue.size}`
        });
      }
      position++;
    }
  } finally {
    matchmakingLock = false;
  }
}

// Periodic ghost user cleanup (runs every 30 seconds)
setInterval(() => {
  let cleaned = 0;
  
  // Clean waitingQueue
  for (const [deviceId, player] of waitingQueue) {
    const socket = io.sockets.sockets.get(player.socketId);
    if (!socket || !socket.connected) {
      waitingQueue.delete(deviceId);
      cleaned++;
    }
  }
  
  // Clean winnersQueue
  for (const [deviceId, player] of winnersQueue) {
    const socket = io.sockets.sockets.get(player.socketId);
    if (!socket || !socket.connected) {
      winnersQueue.delete(deviceId);
      cleaned++;
    }
  }
  
  // Clean playersInMatch (if their match is no longer active)
  for (const deviceId of playersInMatch) {
    let inActiveMatch = false;
    for (const [, match] of matches) {
      if (match.active && match.players[deviceId]) {
        inActiveMatch = true;
        break;
      }
    }
    if (!inActiveMatch) {
      playersInMatch.delete(deviceId);
      cleaned++;
    }
  }
  
  if (cleaned > 0) {
    console.log(`[ghost-cleanup] Removed ${cleaned} stale entries`);
  }
}, 30000);

// Declare the overall tournament champion
async function declareTournamentChampion(player) {
  console.log(`[tournament] 🏆 CHAMPION: ${player.username}`);
  io.emit('tournament_champion', { username: player.username, deviceId: player.deviceId });
  broadcastToSpectators('tournament_champion', { username: player.username });

  const s = io.sockets.sockets.get(player.socketId);
  if (s) s.emit('you_are_champion', { message: '🏆 Congratulations! You are the Tournament Champion!' });

  // Update leaderboard
  const lb = leaderboard.get(player.username) || { username: player.username, wins: 0 };
  lb.stage = 'champion';
  leaderboard.set(player.username, lb);
  broadcastLeaderboard();

  // Persist champion status to MongoDB
  try {
    await TournamentPlayer.findOneAndUpdate(
      { deviceId: player.deviceId, tournamentId: tournamentConfig.scheduledDate },
      { status: 'winner' }
    );
  } catch (e) { console.error('[tournament] DB update champion error:', e.message); }
}

// Reusable function to start the tournament and pair all players (Round 1)
function startTournament() {
  if (tournamentConfig.tournamentStarted) return { error: 'Tournament already started' };
  if (registeredPlayers.size < 2) return { error: 'Need at least 2 registered players' };

  tournamentConfig.tournamentStarted = true;
  currentRound = 1;
  bracketWinners.clear();

  // Update tournament status in DB
  TournamentSchedule.findOneAndUpdate(
    { status: 'scheduled' },
    { status: 'started' }
  ).catch(e => console.error('[tournament] DB status update error:', e.message));

  // Only include players who have an active socket connection
  const allPlayers = [...registeredPlayers.values()];
  const connectedPlayers = allPlayers.filter(p => {
    if (!p.socketId) return false;
    const socket = io.sockets.sockets.get(p.socketId);
    return socket && socket.connected;
  });

  console.log(`[tournament] ${allPlayers.length} registered, ${connectedPlayers.length} connected`);

  if (connectedPlayers.length < 2) {
    tournamentConfig.tournamentStarted = false; // Rollback
    return { error: `Only ${connectedPlayers.length} players connected. Need at least 2.` };
  }

  const players = connectedPlayers;
  
  // Calculate questions per match based on player count
  const questionsPerMatch = getQuestionsPerMatch(connectedPlayers.length);
  console.log(`[tournament] Using ${questionsPerMatch} questions per match for ${connectedPlayers.length} players`);
  
  // Broadcast tournament start with Bible questions bank to all clients
  // Each paired match will get specific questions, but clients need the full bank for display
  io.emit('tournament_started', {
    message: 'Tournament is starting!',
    playerCount: registeredPlayers.size,
    round: 1,
    questionsPerMatch: questionsPerMatch,
    bibleQuestions: BIBLE_QUESTIONS, // Send full question bank to frontend
  });

  // Now pair all registered players for Round 1
  const matchPairs = pairPlayersForRound(players, 1, questionsPerMatch);

  // Notify spectators
  broadcastToSpectators('tournament_started', {
    playerCount: registeredPlayers.size,
    matchCount: matchPairs.length,
    round: 1,
  });

  console.log(`[tournament] 🎮 Started with ${registeredPlayers.size} players, ${matchPairs.length} Round-1 matches`);
  console.log(`[tournament] 📚 Sent ${BIBLE_QUESTIONS.length} Bible questions to all clients`);
  
  return { ok: true, playerCount: registeredPlayers.size, matches: matchPairs, round: 1 };
}

// Schedule auto-start timer for a tournament
function scheduleAutoStart(scheduledDate) {
  // Clear any existing timer
  if (autoStartTimer) {
    clearTimeout(autoStartTimer);
    autoStartTimer = null;
  }

  const startTime = new Date(scheduledDate).getTime();
  const now = Date.now();
  const delay = startTime - now;

  console.log(`[tournament] scheduleAutoStart called:`);
  console.log(`  - Scheduled: ${scheduledDate}`);
  console.log(`  - Server now: ${new Date(now).toISOString()}`);
  console.log(`  - Delay: ${Math.round(delay / 1000)}s (${Math.round(delay / 60000)} min)`);

  if (delay <= 0) {
    // Time already passed — start immediately if possible
    console.log('[tournament] Scheduled time already passed — auto-starting now');
    io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
    attemptTournamentStart();
    return;
  }

  // Schedule countdown warnings at 5min, 1min, 30s, 10s before start
  const countdownWarnings = [
    { ms: 5 * 60 * 1000, msg: '5 minutes' },
    { ms: 1 * 60 * 1000, msg: '1 minute' },
    { ms: 30 * 1000, msg: '30 seconds' },
    { ms: 10 * 1000, msg: '10 seconds' },
    { ms: 5 * 1000, msg: '5 seconds' },
  ];

  countdownWarnings.forEach(({ ms, msg }) => {
    const warningDelay = delay - ms;
    if (warningDelay > 0) {
      setTimeout(() => {
        io.emit('tournament_countdown', { 
          secondsRemaining: Math.round(ms / 1000), 
          message: `Tournament starts in ${msg}!` 
        });
        console.log(`[tournament] ⏱️  Countdown: ${msg} remaining`);
      }, warningDelay);
    }
  });

  console.log(`[tournament] ✅ Auto-start timer SET — will fire in ${Math.round(delay / 1000)}s`);
  autoStartTimer = setTimeout(() => {
    console.log('[tournament] ⏰ Auto-start timer FIRED! Starting tournament...');
    io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
    attemptTournamentStart();
  }, delay);
}

// Attempt to start tournament with retry logic
let autoStartRetryCount = 0;
const MAX_AUTO_START_RETRIES = 6; // Retry for up to 30 seconds (6 x 5s)

function attemptTournamentStart() {
  const result = startTournament();
  
  if (result.error) {
    console.log(`[tournament] Auto-start attempt ${autoStartRetryCount + 1} failed: ${result.error}`);
    
    // Log current state for debugging
    console.log(`[tournament] State: ${registeredPlayers.size} registered, ${getActivePlayerCount()} active`);
    
    // If not enough players and we haven't retried too many times, retry in 5 seconds
    if (autoStartRetryCount < MAX_AUTO_START_RETRIES) {
      autoStartRetryCount++;
      console.log(`[tournament] Retrying in 5 seconds... (attempt ${autoStartRetryCount}/${MAX_AUTO_START_RETRIES})`);
      
      io.emit('tournament_auto_start_pending', {
        message: `Waiting for players... Retry ${autoStartRetryCount}/${MAX_AUTO_START_RETRIES}`,
        registeredCount: registeredPlayers.size,
        activeCount: getActivePlayerCount(),
        retryIn: 5,
      });
      
      setTimeout(() => {
        attemptTournamentStart();
      }, 5000);
    } else {
      // Give up after max retries
      autoStartRetryCount = 0;
      console.log(`[tournament] Auto-start failed after ${MAX_AUTO_START_RETRIES} retries`);
      
      io.emit('tournament_auto_start_failed', { 
        error: result.error,
        message: `Tournament could not start: ${result.error}. Please try starting manually.`,
        registeredCount: registeredPlayers.size,
        activeCount: getActivePlayerCount(),
      });
    }
  } else {
    // Success!
    autoStartRetryCount = 0;
    console.log(`[tournament] ✅ Auto-start successful!`);
  }
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

// Calculate questions per match based on number of players in tournament
function getQuestionsPerMatch(playerCount) {
  // More players = more rounds = can have fewer questions per match
  // Fewer players = fewer rounds = need more questions per match for excitement
  if (playerCount <= 4) return 10;      // 2 rounds max → 10 questions per match
  if (playerCount <= 8) return 7;       // 3 rounds max → 7 questions per match
  if (playerCount <= 16) return 5;      // 4 rounds max → 5 questions per match
  if (playerCount <= 32) return 5;      // 5 rounds max → 5 questions per match
  return 3;                              // 6+ rounds → 3 questions per match (faster games)
}

function createMatch(p1, p2, isSpecialSession = false, questionsCount = 5) {
  const matchId = 'match_' + Date.now() + '_' + Math.random().toString(36).slice(2, 6);
  const seed    = matchId;

  // Pick questions from the right bank
  // Bible quiz (special session) uses Bible questions, normal matches use frontend seeded questions
  let bank = isSpecialSession && BIBLE_QUESTIONS.length > 0
    ? BIBLE_QUESTIONS
    : null;                 // normal: frontend picks from its own QUESTIONS_DB using the seed

  let questions = null;
  if (bank) {
    // Repeat pool if fewer than needed
    let pool = bank;
    while (pool.length < questionsCount) pool = [...pool, ...bank];
    questions = seededShuffle(pool, seed).slice(0, questionsCount);
  }
  // If bank is null, frontend uses getSeededQuestions(questionsCount, [], seed) — same seed = same questions

  const match = {
    matchId,
    seed,
    questions,          // null = use seeded frontend bank; array = use these exact questions
    questionsCount,     // Track how many questions this match should have
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
      
      // IMMEDIATELY remove from queues (ghost cleanup)
      waitingQueue.delete(deviceId);
      winnersQueue.delete(deviceId);
      
      broadcastLobbyCount();
      
      // Broadcast updated active count during tournament registration
      if (isRegistrationMode()) {
        const activeCount = getActivePlayerCount();
        io.emit('active_count', { count: activeCount, registered: registeredPlayers.size });
      }
      
      // Mark player as disconnected in any active match
      for (const [matchId, match] of matches) {
        if (match.players[deviceId] && match.active) {
          match.players[deviceId].connected = false;
          match.players[deviceId].disconnectedAt = Date.now();
          socket.to(matchId).emit('opponent_disconnected', { matchId });
          
          // Give them 15s to reconnect before forfeiting (reduced from 30s for faster games)
          setTimeout(() => {
            const m = matches.get(matchId);
            if (m && m.active && !m.players[deviceId]?.connected) {
              // Forfeit: opponent wins
              const winner = Object.values(m.players).find(p => p.deviceId !== deviceId);
              const loser  = match.players[deviceId];
              
              // Clean up match timer
              cleanupMatchTimer(matchId);
              
              // Remove from playersInMatch
              playersInMatch.delete(deviceId);
              if (winner) playersInMatch.delete(winner.deviceId);
              
              if (winner) {
                const winnerSocket = io.sockets.sockets.get(winner.socketId);
                if (winnerSocket) winnerSocket.emit('match_over_forfeit', { result: 'win', reason: 'Opponent left the match.' });
                // Update leaderboard
                const wb = leaderboard.get(winner.username) || { username: winner.username, wins: 0 };
                wb.wins = (wb.wins || 0) + 1;
                leaderboard.set(winner.username, wb);
                broadcastLeaderboard();
                
                // If this is a tournament match, queue winner for next round
                if (m.tournamentRound) {
                  const round = m.tournamentRound;
                  const wp = registeredPlayers.get(winner.deviceId);
                  if (wp) {
                    wp.wins = (wp.wins || 0) + 1;
                    wp.round = round + 1;
                  }
                  queueWinnerForNextRound(
                    { deviceId: winner.deviceId, username: winner.username, socketId: winner.socketId, wins: (wp?.wins || 1) },
                    round
                  );
                }
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
          }, 15000);
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

  // ── Request current state sync (reconnection / visibility change) ──────
  socket.on('request_state_sync', ({ deviceId }) => {
    if (!deviceId) return;
    
    // Build current state for this player
    const syncData = {
      timestamp: Date.now(),
    };
    
    // Check if in tournament registration mode
    if (isRegistrationMode()) {
      const player = registeredPlayers.get(deviceId);
      if (player) {
        syncData.stage = 'waiting';
        syncData.waitingCount = registeredPlayers.size;
        syncData.scheduledDate = tournamentConfig.scheduledDate;
        syncData.tournamentStarted = false;
      }
    } else if (tournamentConfig.tournamentStarted) {
      syncData.tournamentStarted = true;
    }
    
    // Check if in active match
    if (playersInMatch.has(deviceId)) {
      for (const [matchId, match] of matches) {
        if (match.p1?.deviceId === deviceId || match.p2?.deviceId === deviceId) {
          const isP1 = match.p1?.deviceId === deviceId;
          const opponent = isP1 ? match.p2 : match.p1;
          syncData.stage = 'match';
          syncData.matchId = matchId;
          syncData.opponent = opponent ? { username: opponent.username, id: opponent.deviceId } : null;
          syncData.tournament = {
            phase: 'in_match',
            matchId,
            currentQuestionIndex: match.currentQuestion || 0,
            round: match.tournamentRound || 1,
          };
          break;
        }
      }
    }
    
    // Check if in winners queue (waiting for next round)
    if (winnersQueue.has(deviceId)) {
      syncData.stage = 'waiting';
      syncData.tournament = {
        phase: 'waiting_match',
        round: winnersQueue.get(deviceId).round || currentRound,
      };
    }
    
    socket.emit('state_sync', syncData);
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

    // GUARD: Check if player is already in an active match
    if (playersInMatch.has(deviceId)) {
      console.log(`[join_lobby] ${username} is already in a match — rejecting`);
      socket.emit('already_in_match', { 
        message: 'You are already in an active match.',
        deviceId 
      });
      return;
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
      // If player already registered via REST, just update their socketId
      if (registeredPlayers.has(deviceId)) {
        const rp = registeredPlayers.get(deviceId);
        rp.socketId = socket.id;
        
        const activeCount = getActivePlayerCount();
        socket.emit('tournament_waiting', {
          message: 'You are registered! Waiting for tournament to start...',
          waitingCount: registeredPlayers.size,
          activeCount: activeCount,
          scheduledDate: tournamentConfig.scheduledDate,
        });
        
        // Broadcast updated active count to all clients
        io.emit('active_count', { count: activeCount, registered: registeredPlayers.size });
        
        console.log(`[tournament] ${username} reconnected socket (${registeredPlayers.size} registered, ${activeCount} active)`);
        return;
      }

      // Otherwise check if user exists in DB — they must register via REST API first
      (async () => {
        try {
          // Check if user already exists in DB by deviceId
          let existingUser = await User.findOne({ deviceId });
          
          if (existingUser) {
            // User already exists — register in-memory and let them join
            registeredPlayers.set(deviceId, {
              username: existingUser.username,
              deviceId,
              joinedAt: Date.now(),
              socketId: socket.id,
              wins: 0,
              round: 1,
              status: 'waiting',
            });
            
            if (!leaderboard.has(existingUser.username)) {
              leaderboard.set(existingUser.username, { username: existingUser.username, wins: 0, stage: 'waiting' });
            }
            
            const activeCount = getActivePlayerCount();
            socket.emit('tournament_waiting', {
              message: 'You are registered! Waiting for tournament to start...',
              waitingCount: registeredPlayers.size,
              activeCount: activeCount,
              scheduledDate: tournamentConfig.scheduledDate,
            });
            
            broadcastToSpectators('player_joined', { username: existingUser.username, waitingCount: registeredPlayers.size, activeCount });
            io.emit('waiting_count', { count: registeredPlayers.size });
            io.emit('active_count', { count: activeCount, registered: registeredPlayers.size });
            
            console.log(`[tournament] ${existingUser.username} logged in via socket (${registeredPlayers.size} registered, ${activeCount} active)`);
          } else {
            // User not found — tell them to register first
            socket.emit('registration_error', { 
              error: 'You need to register first. Please enter your username to join.',
              code: 'NOT_REGISTERED'
            });
            console.log(`[tournament] ${username} (${deviceId}) not registered — rejected`);
          }
        } catch (err) {
          console.error(`[tournament] DB error checking ${username}:`, err.message);
          socket.emit('registration_error', { 
            error: 'Connection error. Please try again.',
            code: 'DB_ERROR'
          });
        }
      })();
      
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

  // ── NEW: Explicit queue join for tournament matchmaking ─────────────────
  socket.on('join_queue', ({ deviceId, username }) => {
    if (isRateLimited(socket.id, 'join_queue', 3, 5000)) {
      return recordViolation(socket, 'Rate limit: join_queue');
    }
    
    // Validate
    if (!deviceId || !username) {
      socket.emit('queue_error', { error: 'Missing deviceId or username' });
      return;
    }
    
    // GUARD: Can't join queue if already in match
    if (playersInMatch.has(deviceId)) {
      socket.emit('already_in_match', { message: 'You are already in an active match.' });
      return;
    }
    
    // GUARD: Already in queue
    if (waitingQueue.has(deviceId) || winnersQueue.has(deviceId)) {
      socket.emit('already_in_queue', { 
        message: 'You are already in the matchmaking queue.',
        queueSize: waitingQueue.size + winnersQueue.size
      });
      return;
    }
    
    // Add to waiting queue
    waitingQueue.set(deviceId, {
      deviceId,
      username,
      socketId: socket.id,
      round: 1,
      queuedAt: Date.now(),
      wins: 0,
    });
    
    console.log(`[waitingQueue] ${username} joined (${waitingQueue.size} waiting)`);
    socket.emit('queue_joined', { 
      position: waitingQueue.size,
      message: 'Looking for opponent...'
    });
    
    // Try instant pairing
    tryInstantQueuePair();
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
    // Both correct — continue with another question (no speed tiebreak)
    match.bothCorrectCount = (match.bothCorrectCount || 0) + 1;
    
    // Check if we've exhausted all questions in current set
    if (match.questionIndex >= match.questions.length - 1) {
      // Need more questions — fetch additional ones from the bank
      const usedIds = new Set(match.questions.map(q => q.id));
      const availableQuestions = BIBLE_QUESTIONS.filter(q => !usedIds.has(q.id));
      
      if (availableQuestions.length > 0) {
        // Add 5 more questions (or however many are available)
        const newQuestions = seededShuffle(availableQuestions, match.matchId + '_extra_' + match.bothCorrectCount)
          .slice(0, 5);
        match.questions = [...match.questions, ...newQuestions];
        console.log(`[match] ${match.matchId} both correct ${match.bothCorrectCount}x — added ${newQuestions.length} more questions`);
      } else {
        // Truly exhausted all questions — use speed tiebreak as last resort
        console.log(`[match] ${match.matchId} exhausted all ${BIBLE_QUESTIONS.length} questions — speed tiebreak`);
        p1Result = p1.answerTime <= p2.answerTime ? 'win' : 'lose';
        p2Result = p1Result === 'win' ? 'lose' : 'win';
        matchOver = true;
      }
    }
    
    if (!matchOver) {
      p1Result = 'both_correct';
      p2Result = 'both_correct';
      match.questionIndex++;
      match.questionStartTime = Date.now();
      
      // Reset answers BEFORE sending next question
      p1.answer = null; p1.answerTime = null;
      p2.answer = null; p2.answerTime = null;
      
      // Restart server timer for next question
      cleanupMatchTimer(match.matchId);
      startMatchTimer(match);
      
      // Send the next question to both players
      const nextQuestion = match.questions[match.questionIndex];
      const nextQuestionPayload = {
        questionIndex: match.questionIndex,
        question: nextQuestion,
        bothCorrectCount: match.bothCorrectCount,
        totalQuestions: match.questions.length,
        message: 'Both correct! Here\'s another question.',
      };
      
      [p1, p2].forEach(player => {
        const sock = io.sockets.sockets.get(player.socketId);
        if (sock) sock.emit('next_question', nextQuestionPayload);
      });
      
      // Don't emit round_result for both_correct — next_question is sufficient
      // Just broadcast to spectators and return early
      broadcastToSpectators('both_correct', {
        matchId: match.matchId,
        p1: p1.username,
        p2: p2.username,
        questionIndex: match.questionIndex,
      });
      
      return; // Exit early — don't emit round_result
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

  // At this point, matchOver is always true (both_correct returns early above)
  const winner = p1Result === 'win' ? p1 : p2Result === 'win' ? p2 : null;
  const loser  = p1Result === 'lose' ? p1 : p2Result === 'lose' ? p2 : null;

  // Update leaderboard
  if (winner) {
    const wb = leaderboard.get(winner.username) || { username: winner.username, wins: 0, totalTime: 0 };
    wb.wins = (wb.wins || 0) + 1;
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
  
  // Clean up match timer
  cleanupMatchTimer(match.matchId);
  
  // IMMEDIATELY remove players from playersInMatch (allows re-queueing)
  playersInMatch.delete(p1.deviceId);
  playersInMatch.delete(p2.deviceId);
  
  setTimeout(() => matches.delete(match.matchId), 30000); // clean up after 30s (reduced from 2min)

  // ── Tournament elimination bracket logic ────────────────────────────
  if (match.tournamentRound) {
    const round = match.tournamentRound;

    // Evict loser from tournament
    if (loser) {
      const lp = registeredPlayers.get(loser.deviceId);
      if (lp) lp.status = 'eliminated';
      
      // Remove from any queues
      waitingQueue.delete(loser.deviceId);
      winnersQueue.delete(loser.deviceId);
      
      TournamentPlayer.findOneAndUpdate(
        { deviceId: loser.deviceId, tournamentId: tournamentConfig.scheduledDate },
        { status: 'eliminated' }
      ).catch(e => console.error('[bracket] DB evict error:', e.message));

      const loserSocket = io.sockets.sockets.get(loser.socketId);
      if (loserSocket) loserSocket.emit('tournament_eliminated', {
        message: 'You have been eliminated from the tournament.',
        round,
      });
      console.log(`[tournament R${round}] Eliminated: ${loser.username}`);
    }

    // Queue winner for the next round (both-wrong = no one advances, both eliminated)
    if (winner) {
      const wp = registeredPlayers.get(winner.deviceId);
      if (wp) {
        wp.wins = (wp.wins || 0) + 1;
        wp.round = round + 1;
        wp.status = 'waiting';
      }
      TournamentPlayer.findOneAndUpdate(
        { deviceId: winner.deviceId, tournamentId: tournamentConfig.scheduledDate },
        { $inc: { wins: 1 }, round: round + 1 }
      ).catch(e => console.error('[bracket] DB winner update error:', e.message));

      // Notify winner they advance
      const winnerSocket = io.sockets.sockets.get(winner.socketId);
      if (winnerSocket) {
        winnerSocket.emit('tournament_round_won', {
          message: `You won Round ${round}! Waiting for next round...`,
          round,
          nextRound: round + 1,
          wins: wp?.wins || 1,
        });
      }

      // Queue winner for next round - this will trigger instant pairing if another winner is available
      queueWinnerForNextRound(
        { deviceId: winner.deviceId, username: winner.username, socketId: winner.socketId, wins: (wp?.wins || 1) },
        round
      );
    } else {
      // Both wrong — both eliminated
      waitingQueue.delete(p1.deviceId);
      waitingQueue.delete(p2.deviceId);
      winnersQueue.delete(p1.deviceId);
      winnersQueue.delete(p2.deviceId);
      
      // Check if round is now complete
      const activeRoundMatches = [...matches.values()].filter(m => m.tournamentRound === round && m.active);
      const waitingWinners = bracketWinners.get(round) || [];
      
      if (activeRoundMatches.length === 0) {
        if (waitingWinners.length >= 2) advanceToNextRound(round);
        else if (waitingWinners.length === 1) declareTournamentChampion(waitingWinners[0]);
        else {
          io.emit('tournament_no_winner', { round, message: 'All players eliminated — no champion this round.' });
        }
      }
    }
  }
}

// ─── Tournament player registration (save username + deviceId to MongoDB) ──────
// Called from the frontend when a user wants to join the tournament.
// Also saves to the persistent User collection for general user tracking.
app.post('/api/users', async (req, res) => {
  try {
    let { username, deviceId } = req.body;

    if (!username || !deviceId) {
      return res.status(400).json({ error: 'username and deviceId are required' });
    }

    // Normalize username: trim whitespace and convert to lowercase
    username = String(username).trim().toLowerCase();

    // Validate username
    if (username.length < 3) {
      return res.status(400).json({ error: 'Username must be at least 3 characters' });
    }
    if (username.length > 30) {
      return res.status(400).json({ error: 'Username must be 30 characters or less' });
    }
    // Only allow alphanumeric characters, underscores, and hyphens
    if (!/^[a-z0-9_-]+$/.test(username)) {
      return res.status(400).json({ error: 'Username can only contain letters, numbers, underscores, and hyphens' });
    }
    // Check for reserved/inappropriate usernames
    const reservedUsernames = ['admin', 'administrator', 'system', 'bot', 'null', 'undefined', 'test'];
    if (reservedUsernames.includes(username)) {
      return res.status(400).json({ error: 'This username is not allowed' });
    }

    // Check if device already registered
    const existingUserByDevice = await User.findOne({ deviceId });
    if (existingUserByDevice) {
      return res.status(200).json({ 
        ok: true, 
        alreadyExists: true, 
        message: "You're already in!", 
        user: existingUserByDevice 
      });
    }

    // Check if username is already taken (case-insensitive due to lowercase normalization)
    const existingUserByUsername = await User.findOne({ username });
    if (existingUserByUsername) {
      return res.status(409).json({ error: 'Username is already taken. Please choose another.' });
    }

    // Create new user
    const user = await User.create({ username, deviceId });

    // If registration is open, also register into current tournament
    if (isRegistrationMode()) {
      if (registeredPlayers.has(deviceId)) {
        return res.status(409).json({ error: 'Already registered for this tournament' });
      }

      // Save to MongoDB tournament players collection
      await TournamentPlayer.findOneAndUpdate(
        { deviceId, tournamentId: tournamentConfig.scheduledDate },
        { username, deviceId, tournamentId: tournamentConfig.scheduledDate, status: 'waiting', wins: 0, round: 1 },
        { upsert: true, returnDocument: 'after', runValidators: true }
      );

      // Register in-memory
      registeredPlayers.set(deviceId, {
        username,
        deviceId,
        joinedAt: Date.now(),
        socketId: null, // will be set when socket connects
        wins: 0,
        round: 1,
        status: 'waiting',
      });

      if (!leaderboard.has(username)) {
        leaderboard.set(username, { username, wins: 0, stage: 'waiting' });
      }

      broadcastToSpectators('player_joined', { username, waitingCount: registeredPlayers.size });
      io.emit('waiting_count', { count: registeredPlayers.size });

      console.log(`[tournament] ${username} registered via REST (${registeredPlayers.size} total)`);
      return res.status(201).json({
        ok: true,
        registered: true,
        waitingCount: registeredPlayers.size,
        scheduledDate: tournamentConfig.scheduledDate,
        message: 'Registered! Waiting for tournament to start.',
      });
    }

    res.status(201).json({ ok: true, registered: false, message: 'User saved. No active tournament registration.' });
  } catch (err) {
    console.error('[api/users] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get all players
app.get('/api/users', async (req, res) => {
  try {
    const users = await User.find({}, { username: 1, deviceId: 1, createdAt: 1, _id: 0 })
      .sort({ createdAt: -1 });
    res.json({ ok: true, count: users.length, users });
  } catch (err) {
    console.error('[api/users] GET all error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get total number of registered players
// NOTE: This must come BEFORE /api/users/:deviceId to avoid "count" being treated as a deviceId
app.get('/api/users/count', async (req, res) => {
  try {
    const count = await User.countDocuments();
    res.json({ ok: true, count });
  } catch (err) {
    console.error('[api/users/count] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get user by username (for frontend validation of cached users)
// NOTE: This must come BEFORE /api/users/:deviceId to avoid "username" being treated as a deviceId
app.get('/api/users/username/:username', async (req, res) => {
  try {
    // Normalize username to lowercase for case-insensitive lookup
    const username = String(req.params.username).trim().toLowerCase();
    const user = await User.findOne({ username });
    if (!user) return res.status(404).json({ error: 'User not found' });
    res.json({ ok: true, user: { username: user.username, deviceId: user.deviceId, createdAt: user.createdAt } });
  } catch (err) {
    console.error('[api/users/username] Error:', err.message);
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
app.post('/admin/login', (req, res) => {
  const { email, password } = req.body;

  if (!email || !password) {
    return res.status(400).json({ error: 'email and password are required' });
  }

  if (email !== ADMIN_EMAIL || password !== ADMIN_PASSWORD) {
    return res.status(401).json({ error: 'Invalid credentials' });
  }

  const token = jwt.sign(
    { email },
    process.env.JWT_SECRET,
    { expiresIn: '24h' }
  );

  res.json({ ok: true, token, admin: { email } });
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

// ─── Debug/Diagnostic endpoint ────────────────────────────────────────────────
// Returns current state of all queues and matches for debugging
app.get('/debug/state', (_, res) => {
  const activeMatches = [...matches.values()].filter(m => m.active);
  
  res.json({
    timestamp: new Date().toISOString(),
    queues: {
      waitingQueue: {
        size: waitingQueue.size,
        players: [...waitingQueue.values()].map(p => ({
          username: p.username,
          deviceId: p.deviceId.slice(0, 8) + '...',
          queuedAt: new Date(p.queuedAt).toISOString(),
          round: p.round,
        })),
      },
      winnersQueue: {
        size: winnersQueue.size,
        players: [...winnersQueue.values()].map(p => ({
          username: p.username,
          deviceId: p.deviceId.slice(0, 8) + '...',
          round: p.round,
          wins: p.wins,
        })),
      },
    },
    matches: {
      total: matches.size,
      active: activeMatches.length,
      activeList: activeMatches.map(m => ({
        matchId: m.matchId,
        round: m.tournamentRound,
        questionIndex: m.questionIndex,
        players: Object.values(m.players).map(p => ({
          username: p.username,
          answered: p.answer !== null,
          connected: p.connected,
        })),
      })),
    },
    playersInMatch: playersInMatch.size,
    bracketWinners: [...bracketWinners.entries()].map(([round, players]) => ({
      round,
      count: players.length,
      players: players.map(p => p.username),
    })),
    matchTimers: matchTimers.size,
    tournament: {
      scheduledDate: tournamentConfig.scheduledDate,
      started: tournamentConfig.tournamentStarted,
      registeredCount: registeredPlayers.size,
      activeCount: getActivePlayerCount(),
      currentRound,
    },
    lobby: lobby.size,
  });
});

// ─── Bible Questions endpoint (for tournament) ───────────────────────────────
// Returns the full Bible questions bank for the tournament
app.get('/api/bible-questions', (_, res) => {
  res.json({
    ok: true,
    count: BIBLE_QUESTIONS.length,
    questions: BIBLE_QUESTIONS,
  });
});

// ─── Tournament REST endpoints ───────────────────────────────────────────────
// Get tournament status (public)
app.get('/tournament/status', (_, res) => {
  const activePlayers = getActivePlayers();
  res.json({
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    registrationOpen: isRegistrationMode(),
    registeredCount: registeredPlayers.size,
    activeCount: activePlayers.length,
    players: [...registeredPlayers.values()].map(p => {
      const socket = p.socketId ? io.sockets.sockets.get(p.socketId) : null;
      const isOnline = socket && socket.connected;
      return { username: p.username, joinedAt: p.joinedAt, isOnline };
    }),
  });
});

// Get scheduled date and check if it's time to start (public)
app.get('/tournament/schedule', (_, res) => {
  const scheduledDate = tournamentConfig.scheduledDate;
  
  if (!scheduledDate) {
    return res.json({
      ok: true,
      scheduled: false,
      scheduledDate: null,
      timeUntilStart: null,
      isTimeToStart: false,
      tournamentStarted: tournamentConfig.tournamentStarted,
    });
  }

  const now = Date.now();
  const startTime = new Date(scheduledDate).getTime();
  const timeUntilStart = startTime - now; // milliseconds until start (negative if past)
  const isTimeToStart = timeUntilStart <= 0;

  res.json({
    ok: true,
    scheduled: true,
    scheduledDate,
    scheduledDateFormatted: new Date(scheduledDate).toLocaleString(),
    timeUntilStart,                          // ms until start (negative = already past)
    timeUntilStartSeconds: Math.floor(timeUntilStart / 1000),
    isTimeToStart,                           // true when now >= scheduledDate
    tournamentStarted: tournamentConfig.tournamentStarted,
    registrationOpen: isRegistrationMode(),
    registeredCount: registeredPlayers.size,
  });
});

// Admin: Set the bible quiz date & time — opens registration
// Protected: requires admin JWT
// Body: { date: '2026-03-20', time: '18:00' }  OR  { scheduledDate: '<ISO string>' }
app.post('/admin/tournament/set-schedule', requireAdmin, async (req, res) => {
  try {
    const { date, time, scheduledDate: isoOverride } = req.body;

    let scheduledDate = isoOverride || null;

    if (!scheduledDate) {
      if (!date || !time) {
        return res.status(400).json({ error: 'Provide either { date, time } or { scheduledDate } (ISO string)' });
      }
      // Combine date (YYYY-MM-DD) + time (HH:MM) into a full ISO string
      scheduledDate = new Date(`${date}T${time}:00`).toISOString();
    }

    if (isNaN(new Date(scheduledDate).getTime())) {
      return res.status(400).json({ error: 'Invalid date/time value' });
    }

    // Save to MongoDB
    await TournamentSchedule.findOneAndUpdate(
      { status: 'scheduled' },
      { scheduledDate: new Date(scheduledDate), status: 'scheduled', registeredCount: 0 },
      { upsert: true, returnDocument: 'after' }
    );

    tournamentConfig.scheduledDate = scheduledDate;
    tournamentConfig.tournamentStarted = false;
    registeredPlayers.clear();
    bracketWinners.clear();
    currentRound = 1;

    scheduleAutoStart(scheduledDate);

    io.emit('tournament_config_updated', {
      scheduledDate,
      registrationOpen: true,
      tournamentStarted: false,
    });

    console.log(`[tournament] Bible quiz scheduled for ${scheduledDate} — registration open (saved to DB)`);
    res.json({ ok: true, scheduledDate, message: 'Bible quiz scheduled! Registration is now open.' });
  } catch (err) {
    console.error('[admin/tournament/set-schedule] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: Schedule a tournament (legacy alias — kept for backward compat)
app.post('/admin/tournament/schedule', requireAdmin, async (req, res) => {
  try {
    const { scheduledDate } = req.body;
    if (!scheduledDate) {
      return res.status(400).json({ error: 'scheduledDate is required (ISO string)' });
    }

    // Save to MongoDB
    await TournamentSchedule.findOneAndUpdate(
      { status: 'scheduled' },
      { scheduledDate: new Date(scheduledDate), status: 'scheduled', registeredCount: 0 },
      { upsert: true, returnDocument: 'after' }
    );

    // Update in-memory config
    tournamentConfig.scheduledDate = scheduledDate;
    tournamentConfig.tournamentStarted = false;
    registeredPlayers.clear();
    bracketWinners.clear();
    currentRound = 1;
    scheduleAutoStart(scheduledDate);
    io.emit('tournament_config_updated', { scheduledDate, registrationOpen: true, tournamentStarted: false });
    console.log(`[tournament] Scheduled for ${scheduledDate} — registration open (saved to DB)`);
    res.json({ ok: true, scheduledDate, message: 'Registration is now open!' });
  } catch (err) {
    console.error('[admin/tournament/schedule] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: Get all registered players
app.get('/admin/tournament/players', (_, res) => {
  res.json({
    players: [...registeredPlayers.values()],
    count: registeredPlayers.size,
    config: tournamentConfig,
  });
});

// Debug: Check tournament timer status
app.get('/admin/tournament/debug', (_, res) => {
  const now = Date.now();
  const scheduledTime = tournamentConfig.scheduledDate ? new Date(tournamentConfig.scheduledDate).getTime() : null;
  const timeUntilStart = scheduledTime ? scheduledTime - now : null;
  
  res.json({
    serverTime: new Date(now).toISOString(),
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    autoStartTimerActive: autoStartTimer !== null,
    timeUntilStartMs: timeUntilStart,
    timeUntilStartSeconds: timeUntilStart ? Math.round(timeUntilStart / 1000) : null,
    timeUntilStartMinutes: timeUntilStart ? Math.round(timeUntilStart / 60000) : null,
    registeredCount: registeredPlayers.size,
    activeCount: getActivePlayerCount(),
    autoStartRetryCount,
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
  
  // Clear new queues
  waitingQueue.clear();
  winnersQueue.clear();
  playersInMatch.clear();
  bracketWinners.clear();
  
  // Clear all match timers
  for (const [matchId] of matchTimers) {
    cleanupMatchTimer(matchId);
  }
  
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
  
  // Clear new queues
  waitingQueue.clear();
  winnersQueue.clear();
  playersInMatch.clear();
  bracketWinners.clear();
  
  // Clear all match timers
  for (const [matchId] of matchTimers) {
    cleanupMatchTimer(matchId);
  }
  
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

let mongoConnected = false;

async function connectMongo(retryCount = 0) {
  const maxRetries = 5;
  try {
    await mongoose.connect(process.env.MONGO_URI);
    mongoConnected = true;
    console.log('✅ Connected to MongoDB');

    // Load persisted tournament schedule from MongoDB on startup
    try {
      const savedSchedule = await TournamentSchedule.findOne({ status: 'scheduled' });
      if (savedSchedule && savedSchedule.scheduledDate) {
        const isoDate = savedSchedule.scheduledDate.toISOString();
        tournamentConfig.scheduledDate = isoDate;
        tournamentConfig.tournamentStarted = false;
        console.log(`✅ Loaded tournament schedule from DB: ${isoDate}`);

        // Re-schedule auto-start if the time hasn't passed yet
        scheduleAutoStart(isoDate);
      }
    } catch (scheduleErr) {
      console.error('⚠️ Could not load tournament schedule:', scheduleErr.message);
    }
    
    return true;
  } catch (err) {
    console.error(`❌ MongoDB connection error (attempt ${retryCount + 1}/${maxRetries}):`, err.message);
    
    if (retryCount < maxRetries - 1) {
      console.log(`   Retrying in 5 seconds...`);
      await new Promise(resolve => setTimeout(resolve, 5000));
      return connectMongo(retryCount + 1);
    }
    
    console.error('❌ MongoDB connection failed after max retries. Server will run without DB.');
    return false;
  }
}

async function startServer() {
  // Try to connect to MongoDB, but don't fail if it doesn't work
  await connectMongo();

  server.listen(PORT, () => {
    console.log(`\n🚀 QuizDuel server listening on http://localhost:${PORT}`);
    if (!mongoConnected) {
      console.log('⚠️  Running without MongoDB - some features may be limited\n');
    } else {
      console.log('');
    }
  });
}

startServer();
