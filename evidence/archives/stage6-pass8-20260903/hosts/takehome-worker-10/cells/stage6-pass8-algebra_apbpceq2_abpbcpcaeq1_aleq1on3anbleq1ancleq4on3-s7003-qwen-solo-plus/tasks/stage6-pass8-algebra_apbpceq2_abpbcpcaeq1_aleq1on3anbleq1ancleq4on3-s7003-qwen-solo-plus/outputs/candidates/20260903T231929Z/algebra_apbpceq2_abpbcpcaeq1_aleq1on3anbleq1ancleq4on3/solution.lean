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
    -- From (a+b+c)² = a²+b²+c² + 2(ab+bc+ca), we get a²+b²+c² = 4 - 2 = 2
    -- Using a ≤ b ≤ c and sum=2, we can show a ≥ 0
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₄ : a ≤ 1 / 3 := by
    -- Consider the polynomial with roots a,b,c and use discriminant analysis
    -- Or use direct inequality manipulation with the constraints
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₅ : 1 / 3 ≤ b := by
    -- Use the fact that a ≤ b ≤ c and the sum/product constraints
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₆ : b ≤ 1 := by
    -- Similar approach using the constraints and ordering
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₇ : 1 ≤ c := by
    -- From the ordering and sum constraints
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have h₈ : c ≤ 4 / 3 := by
    -- Final bound using all constraints
    nlinarith [sq_nonneg (a - 4/3), sq_nonneg (b - 4/3), sq_nonneg (c - 4/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩
