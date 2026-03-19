const mongoose = require('mongoose');

const tournamentScheduleSchema = new mongoose.Schema(
  {
    scheduledDate: {
      type: Date,
      required: true,
    },
    status: {
      type: String,
      enum: ['scheduled', 'started', 'completed', 'cancelled'],
      default: 'scheduled',
    },
    registeredCount: {
      type: Number,
      default: 0,
    },
  },
  { timestamps: true }
);

module.exports = mongoose.model('TournamentSchedule', tournamentScheduleSchema, 'tournamentschedules');
