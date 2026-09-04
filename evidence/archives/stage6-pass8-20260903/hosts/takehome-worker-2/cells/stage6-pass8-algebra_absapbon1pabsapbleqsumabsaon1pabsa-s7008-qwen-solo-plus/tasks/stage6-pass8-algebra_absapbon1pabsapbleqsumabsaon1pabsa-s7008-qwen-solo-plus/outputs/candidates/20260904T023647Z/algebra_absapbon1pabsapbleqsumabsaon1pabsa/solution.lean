import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absapbon1pabsapbleqsumabsaon1pabsa
  (a b : ℝ) :
  abs (a + b) / (1 + abs (a + b)) ≤ abs a / (1 + abs a) + abs b / (1 + abs b) := by first | omega | norm_num | nlinarith | linarith | ring | aesop | simp_all
