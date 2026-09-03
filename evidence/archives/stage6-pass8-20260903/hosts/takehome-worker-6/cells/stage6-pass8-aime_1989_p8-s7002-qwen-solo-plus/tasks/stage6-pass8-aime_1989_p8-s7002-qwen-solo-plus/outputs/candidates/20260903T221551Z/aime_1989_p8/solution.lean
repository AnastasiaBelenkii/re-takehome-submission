import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  have h_poly : 
    3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
    - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
    + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) 
    = 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g := by
    ring
  calc
    16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g
      = 3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
        - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
        + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) := by rw [h_poly]
    _ = 3 * 123 - 3 * 12 + 1 := by rw [h₂, h₁, h₀]
    _ = 334 := by norm_num
