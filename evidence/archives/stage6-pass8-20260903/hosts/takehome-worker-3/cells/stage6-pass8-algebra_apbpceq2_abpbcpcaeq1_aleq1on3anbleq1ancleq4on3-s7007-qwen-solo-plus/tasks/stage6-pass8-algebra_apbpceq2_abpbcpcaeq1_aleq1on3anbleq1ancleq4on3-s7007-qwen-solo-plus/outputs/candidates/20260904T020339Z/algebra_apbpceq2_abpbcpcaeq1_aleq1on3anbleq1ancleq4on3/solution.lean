import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h_sum_sq : a^2 + b^2 + c^2 = 2 := by
    have h3 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h₁] at h3
    rw [h₂] at h3
    linarith
  
  have ha_nonneg : 0 ≤ a := by
    by_contra h
    have h₃ : a < 0 := by linarith
    have h₄ : b ≥ 0 := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
    have h₅ : c ≥ 0 := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (b + c), sq_nonneg (c + a)]
    nlinarith [sq_pos_of_neg h₃]
  
  have ha_le_third : a ≤ 1 / 3 := by
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have hb_ge_third : 1 / 3 ≤ b := by
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have hb_le_one : b ≤ 1 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have hc_ge_one : 1 ≤ c := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  have hc_le_fourthirds : c ≤ 4 / 3 := by
    nlinarith [sq_nonneg (a - 4/3), sq_nonneg (b - 4/3), sq_nonneg (c - 4/3),
      mul_nonneg (sub_nonneg.mpr h₀.1) (sub_nonneg.mpr h₀.2)]
  
  exact ⟨ha_nonneg, ha_le_third, hb_ge_third, hb_le_one, hc_ge_one, hc_le_fourthirds⟩
