import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1989_p8
  (a b c d e f g : ℝ)
  (h₀ : a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g = 1)
  (h₁ : 4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g = 12)
  (h₂ : 9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g = 123) :
  16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
  -- Define the target expression
  have h₃ : 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g = 334 := by
    -- Use linear combination: target = 3*h₂ - 3*h₁ + h₀
    -- Extract the left-hand sides from the hypotheses
    have h₄ : 3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
             - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
             + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) 
             = 3 * 123 - 3 * 12 + 1 := by
      calc
        3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
          - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
          + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g)
            = 3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
              - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
              + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) := rfl
        _ = 3 * 123 - 3 * 12 + 1 := by
          rw [h₂, h₁, h₀]
          <;> ring_nf
    -- Simplify the right side
    norm_num at h₄
    -- Expand the left side to verify it equals the target expression
    have h₅ : 3 * (9 * a + 16 * b + 25 * c + 36 * d + 49 * e + 64 * f + 81 * g) 
             - 3 * (4 * a + 9 * b + 16 * c + 25 * d + 36 * e + 49 * f + 64 * g) 
             + (a + 4 * b + 9 * c + 16 * d + 25 * e + 36 * f + 49 * g) 
             = 16 * a + 25 * b + 36 * c + 49 * d + 64 * e + 81 * f + 100 * g := by
      ring_nf
    -- Combine to get the result
    linarith
  exact h₃
