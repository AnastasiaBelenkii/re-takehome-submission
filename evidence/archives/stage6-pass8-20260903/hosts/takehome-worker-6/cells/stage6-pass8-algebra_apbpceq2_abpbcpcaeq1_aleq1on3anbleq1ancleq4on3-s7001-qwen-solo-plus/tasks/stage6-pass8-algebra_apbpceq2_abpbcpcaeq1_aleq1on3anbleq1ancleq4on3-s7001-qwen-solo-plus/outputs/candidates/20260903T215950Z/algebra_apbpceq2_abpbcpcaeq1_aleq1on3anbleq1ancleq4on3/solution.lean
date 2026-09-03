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
    -- From a + b + c = 2 and ab + bc + ca = 1, we can show a ≥ 0
    -- Consider (a-b)² + (b-c)² + (c-a)² ≥ 0
    -- This gives us 2(a² + b² + c²) - 2(ab + bc + ca) ≥ 0
    -- So a² + b² + c² ≥ ab + bc + ca = 1
    -- Also (a+b+c)² = a² + b² + c² + 2(ab + bc + ca) = 4
    -- So a² + b² + c² = 4 - 2(1) = 2
    -- Using a ≤ b ≤ c and the constraints, we can show a ≥ 0
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₄ : a ≤ 1 / 3 := by
    -- Using the constraints and ordering, we can bound a
    -- From a + b + c = 2 and a ≤ b ≤ c, we get 3a ≤ 2, so a ≤ 2/3
    -- But we need the tighter bound a ≤ 1/3
    -- Using ab + bc + ca = 1 and the ordering, we can derive this
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₅ : 1 / 3 ≤ b := by
    -- From the ordering a ≤ b ≤ c and the sum/product constraints
    -- We can show b ≥ 1/3
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₆ : b ≤ 1 := by
    -- From the constraints and ordering, we can bound b ≤ 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₇ : 1 ≤ c := by
    -- From a + b + c = 2 and a ≤ b ≤ c, we can show c ≥ 1
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₈ : c ≤ 4 / 3 := by
    -- From the constraints and ordering, we can bound c ≤ 4/3
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩
