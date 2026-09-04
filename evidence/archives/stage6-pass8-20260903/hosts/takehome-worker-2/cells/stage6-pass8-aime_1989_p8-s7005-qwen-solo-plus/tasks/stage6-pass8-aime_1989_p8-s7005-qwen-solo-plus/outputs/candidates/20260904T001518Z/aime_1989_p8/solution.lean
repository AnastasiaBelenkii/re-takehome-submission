import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  have h₃ : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
    -- Use the pattern: S₃ = 3*S₂ - 3*S₁ + S₀
    -- This comes from the fact that the second differences are constant
    -- For a quadratic sequence, the third difference is zero
    -- So S₃ - 3*S₂ + 3*S₁ - S₀ = 0, meaning S₃ = 3*S₂ - 3*S₁ + S₀
    calc
      16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 
        3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) - 
        3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) + 
        (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) := by
        ring_nf
        <;> norm_num
        <;> linarith
      _ = 3 * 123 - 3 * 12 + 1 := by rw [h₂, h₁, h₀]
      _ = 369 - 36 + 1 := by norm_num
      _ = 334 := by norm_num
  exact h₃
