// Isolated transcription of the uploaded HTML arithmetic; no DOM or uploaded code executes.
// This checks these five JavaScript fixtures, not universal floating-point equivalence.
import assert from 'node:assert/strict';
const fixtures = [[558, 12, 0], [284, 5, 120], [306.04, 5, 72],
  [552.87, 5, 50], [247.53, 5, 18]];
for (const [period, harmonic, expected] of fixtures) {
  const step1 = period * 12;
  const step2_rem = step1 % 360;
  const step3 = Math.floor(step2_rem);
  const step4 = step3 * harmonic;
  const step5_rem = step4 % 144;
  assert.equal(step5_rem, expected);
  console.log(JSON.stringify({period, harmonic, result: step5_rem}));
}
