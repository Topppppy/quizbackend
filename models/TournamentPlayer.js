const mongoose = require('mongoose');

const tournamentPlayerSchema = new mongoose.Schema(
  {
    username: {
      type: String,
      required: true,
      trim: true,
      maxlength: 30,
    },
    deviceId: {
      type: String,
      required: true,
      // Note: unique constraint is now a compound index with tournamentId (see below)
    },
    // Which tournament session they belong to (ISO date string of scheduledDate)
    tournamentId: {
      type: String,
      required: true,
    },
    // Tournament progression
    status: {
      type: String,
      enum: ['waiting', 'playing', 'eliminated', 'winner'],
      default: 'waiting',
    },
    wins: {
      type: Number,
      default: 0,
    },
    round: {
      type: Number,
      default: 1,
    },
  },
  { timestamps: true }
);

// Compound unique index: same device can join different tournaments, but only once per tournament
tournamentPlayerSchema.index({ deviceId: 1, tournamentId: 1 }, { unique: true });

module.exports = mongoose.model('TournamentPlayer', tournamentPlayerSchema);
