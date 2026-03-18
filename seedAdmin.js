/**
 * Seed script — creates the first admin account.
 *
 * Usage:
 *   node seedAdmin.js <email> <password>
 *
 * Example:
 *   node seedAdmin.js admin@quiz.com supersecret123
 */
require('dotenv').config();
const mongoose = require('mongoose');
const Admin = require('./models/Admin');

async function seed() {
  const [,, email, password] = process.argv;

  if (!email || !password) {
    console.error('Usage: node seedAdmin.js <email> <password>');
    process.exit(1);
  }

  await mongoose.connect(process.env.MONGO_URI);
  console.log('Connected to MongoDB');

  const existing = await Admin.findOne({ email });
  if (existing) {
    console.log(`Admin with email "${email}" already exists.`);
    process.exit(0);
  }

  await Admin.create({ email, password });
  console.log(`✅ Admin created: ${email}`);
  process.exit(0);
}

seed().catch((err) => {
  console.error(err);
  process.exit(1);
});
