import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  -- Define the target expression as T
  -- Compute h₁ - h₀ to get the first difference
  have h_diff1 : 3 * a + 5 * b + 7 * c + 9 * d + 11 * e + 13 * f + 15 * g = 11 := by
    linarith
  -- Compute h₂ - h₁ to get another first difference
  have h_diff2 : 5 * a + 7 * b + 9 * c + 11 * d + 13 * e + 15 * f + 17 * g = 111 := by
    linarith
  -- Compute h_diff2 - h_diff1 to get the second difference
  have h_diff3 : 2 * a + 2 * b + 2 * c + 2 * d + 2 * e + 2 * f + 2 * g = 100 := by
    linarith
  -- Now compute the next first difference: h_diff2 + h_diff3
  have h_diff4 : 7 * a + 9 * b + 11 * c + 13 * d + 15 * e + 17 * f + 19 * g = 211 := by
    linarith
  -- Finally compute the target by adding h_diff4 to h₂
  linarith
