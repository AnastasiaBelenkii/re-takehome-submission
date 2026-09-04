import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  -- Case analysis on the sign of x-1, x, and x+1
  have h₁ : 0 ≤ x := by
    by_contra hx
    -- If x < 0, then abs x = -x
    have h₂ : x < 0 := by linarith
    -- Consider subcases based on whether x < -1 or -1 ≤ x < 0
    cases' lt_or_ge x (-1) with h₃ h₃
    · -- Case: x < -1
      have h₄ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg (by linarith)]
      have h₅ : abs x = -x := by
        rw [abs_of_neg h₂]
      have h₆ : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg (by linarith)]
      rw [h₄, h₅, h₆] at h₀
      linarith
    · -- Case: -1 ≤ x < 0
      have h₄ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg (by linarith)]
      have h₅ : abs x = -x := by
        rw [abs_of_neg h₂]
      have h₆ : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg (by linarith)]
      rw [h₄, h₅, h₆] at h₀
      linarith
  have h₂ : x ≤ 1 := by
    by_contra hx
    -- If x > 1, then abs (x-1) = x-1, abs x = x, abs (x+1) = x+1
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
