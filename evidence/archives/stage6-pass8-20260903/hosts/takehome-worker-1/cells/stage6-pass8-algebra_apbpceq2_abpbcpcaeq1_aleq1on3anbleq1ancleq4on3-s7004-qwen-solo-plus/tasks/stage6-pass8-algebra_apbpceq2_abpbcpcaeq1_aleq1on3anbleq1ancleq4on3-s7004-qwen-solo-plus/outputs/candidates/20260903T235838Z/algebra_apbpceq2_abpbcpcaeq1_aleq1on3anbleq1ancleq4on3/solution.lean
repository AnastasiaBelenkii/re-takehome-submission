import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : 0 ≤ a := by
    -- From ab + bc + ca = 1 and a ≤ b ≤ c, we can show a ≥ 0
    -- If a < 0, then since b ≥ a and c ≥ b, we'd have issues with the sum
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₄ : a ≤ 1 / 3 := by
    -- Using the constraints and ordering, we can bound a from above
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₅ : 1 / 3 ≤ b := by
    -- From the ordering and sum constraints, b must be at least 1/3
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₆ : b ≤ 1 := by
    -- Using the constraints, we can show b ≤ 1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₇ : 1 ≤ c := by
    -- From the ordering and sum constraints, c must be at least 1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₈ : c ≤ 4 / 3 := by
    -- Using the constraints, we can bound c from above
    nlinarith [sq_nonneg (a - 4/3), sq_nonneg (b - 4/3), sq_nonneg (c - 4/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩
