import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  -- Proof Sketch for 0 <= x:
  -- We proceed by contradiction. Assume x < 0.
  -- We split into two cases: x < -1 and -1 <= x < 0.
  -- In the first case, the equation simplifies to -3x = x + 2, yielding x = -1/2, which contradicts x < -1.
  -- In the second case, the equation simplifies to 2 - x = x + 2, yielding x = 0, which contradicts x < 0.
  -- Thus, x must be >= 0.
  have h₁ : 0 ≤ x := by
    by_contra hx
    have hx_neg : x < 0 := by linarith
    by_cases h_lt_neg_one : x < -1
    · -- Case x < -1
      have h_abs_sub : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg hx_neg]
      have h_abs_add : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg (by linarith)]
      rw [h_abs_sub, h_abs_x, h_abs_add] at h₀
      linarith
    · -- Case -1 <= x < 0
      have h_ge_neg_one : -1 ≤ x := by linarith
      have h_abs_sub : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg hx_neg]
      have h_abs_add : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg (by linarith)]
      rw [h_abs_sub, h_abs_x, h_abs_add] at h₀
      linarith
  
  -- Proof Sketch for x <= 1:
  -- We proceed by contradiction. Assume x > 1.
  -- All absolute value terms become positive expressions.
  -- The equation simplifies to 3x = x + 2, yielding x = 1, which contradicts x > 1.
  -- Thus, x must be <= 1.
  have h₂ : x ≤ 1 := by
    by_contra hx
    have hx_gt_one : 1 < x := by linarith
    have h_abs_sub : abs (x - 1) = x - 1 := by
      rw [abs_of_pos (by linarith)]
    have h_abs_x : abs x = x := by
      rw [abs_of_pos (by linarith)]
    have h_abs_add : abs (x + 1) = x + 1 := by
      rw [abs_of_pos (by linarith)]
    rw [h_abs_sub, h_abs_x, h_abs_add] at h₀
    linarith
  
  exact ⟨h₁, h₂⟩
