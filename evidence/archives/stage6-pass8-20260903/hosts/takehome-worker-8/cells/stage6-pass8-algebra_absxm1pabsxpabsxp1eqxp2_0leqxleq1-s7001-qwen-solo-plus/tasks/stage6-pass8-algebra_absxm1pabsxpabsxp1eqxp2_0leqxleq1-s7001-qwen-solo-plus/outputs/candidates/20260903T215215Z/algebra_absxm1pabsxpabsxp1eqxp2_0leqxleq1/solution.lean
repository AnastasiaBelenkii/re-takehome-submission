import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  constructor
  · -- Prove 0 ≤ x
    by_contra hx
    have hx_neg : x < 0 := by linarith
    -- Case analysis on whether x ≤ -1 or x ≥ -1
    cases' le_total x (-1) with h_le h_ge
    · -- Case x ≤ -1
      have h_abs_x_minus_1 : abs (x - 1) = 1 - x := by
        rw [abs_of_nonpos] <;> linarith
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg] <;> linarith
      have h_abs_x_plus_1 : abs (x + 1) = -(x + 1) := by
        rw [abs_of_nonpos] <;> linarith
      have h_sum : abs (x - 1) + abs x + abs (x + 1) = -3 * x := by
        rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
        ring
      have h_eq : -3 * x = x + 2 := by linarith
      have h_sol : x = -1 / 2 := by linarith
      linarith
    · -- Case x ≥ -1
      have h_abs_x_minus_1 : abs (x - 1) = 1 - x := by
        rw [abs_of_nonpos] <;> linarith
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg] <;> linarith
      have h_abs_x_plus_1 : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg] <;> linarith
      have h_sum : abs (x - 1) + abs x + abs (x + 1) = 2 - x := by
        rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
        ring
      have h_eq : 2 - x = x + 2 := by linarith
      have h_sol : x = 0 := by linarith
      linarith
  · -- Prove x ≤ 1
    by_contra hx
    have hx_gt_1 : x > 1 := by linarith
    have h_abs_x_minus_1 : abs (x - 1) = x - 1 := by
      rw [abs_of_pos] <;> linarith
    have h_abs_x : abs x = x := by
      rw [abs_of_pos] <;> linarith
    have h_abs_x_plus_1 : abs (x + 1) = x + 1 := by
      rw [abs_of_pos] <;> linarith
    have h_sum : abs (x - 1) + abs x + abs (x + 1) = 3 * x := by
      rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
      ring
    have h_eq : 3 * x = x + 2 := by linarith
    have h_sol : x = 1 := by linarith
    linarith
