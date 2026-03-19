const mongoose = require('mongoose');

const userSchema = new mongoose.Schema(
  {
    username: {
      type: String,
      required: true,
      unique: true,           // Enforce uniqueness at DB level
      trim: true,
      lowercase: true,        // Auto-convert to lowercase
      minlength: 3,
      maxlength: 30,
      match: [/^[a-z0-9_-]+$/, 'Username can only contain letters, numbers, underscores, and hyphens'],
    },
    deviceId: {
      type: String,
      required: true,
      unique: true,
    },
  },
  { timestamps: true }
);

module.exports = mongoose.model('User', userSchema, 'users');
