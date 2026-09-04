import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_sqineq_unitcircatbpabsamblt1
  (a b: ℝ)
  (h₀ : a^2 + b^2 = 1) :
  a * b + |a - b| ≤ 1 := by
  by_cases h₁ : a ≥ b
  · -- Case: a ≥ b, so |a - b| = a - b
    have h₂ : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr h₁)
    rw [h₂]
    -- Use the fact that (a - b)^2 = 1 - 2ab to bound the expression
    have h₃ : (a - b)^2 = 1 - 2 * a * b := by
      calc
        (a - b)^2 = a^2 - 2 * a * b + b^2 := by ring
        _ = (a^2 + b^2) - 2 * a * b := by ring
        _ = 1 - 2 * a * b := by rw [h₀]
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a - b - 1)]
  · -- Case: ¬ (a ≥ b)
    have h₂ : a < b := lt_of_not_ge h₁
    have h₃ : |a - b| = b - a := by
      rw [abs_of_neg (sub_neg_of_lt h₂), neg_sub]
    rw [h₃]
    have h₄ : (a - b)^2 = 1 - 2 * a * b := by
      calc
        (a - b)^2 = a^2 - 2 * a * b + b^2 := by ring
        _ = (a^2 + b^2) - 2 * a * b := by ring
        _ = 1 - 2 * a * b := by rw [h₀]
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (b - a - 1)]
