import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h₁ : 0 ≤ x := by
    by_contra h
    have h₂ : x < 0 := by linarith
    by_cases h₃ : x < -1
    · -- Case: x < -1
      have h₄ : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h₅ : abs x = -x := by
        rw [abs_of_neg h₂]
      have h₆ : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg (by linarith)]
      rw [h₄, h₅, h₆] at h₀
      linarith
    · -- Case: -1 ≤ x < 0
      have h₄ : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h₅ : abs x = -x := by
        rw [abs_of_neg h₂]
      have h₆ : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg (by linarith)]
      rw [h₄, h₅, h₆] at h₀
      linarith
  
  have h₂ : x ≤ 1 := by
    by_contra h
    have h₃ : x > 1 := by linarith
    have h₄ : abs (x - 1) = x - 1 := by
      rw [abs_of_pos (by linarith)]
    have h₅ : abs x = x := by
      rw [abs_of_pos (by linarith)]
    have h₆ : abs (x + 1) = x + 1 := by
      rw [abs_of_pos (by linarith)]
    rw [h₄, h₅, h₆] at h₀
    linarith
  
  exact ⟨h₁, h₂⟩
