import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2
  
  -- Lemma: sqrt(ab) = sqrt(a) * sqrt(b)
  have h_sqrt_mul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul (le_of_lt ha)]
  
  -- Identity: (a+b)/2 - sqrt(ab) = (sqrt(a) - sqrt(b))^2 / 2
  have h_identity : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b)^2 / 2 := by
    calc
      (a + b) / 2 - Real.sqrt (a * b) = (a + b) / 2 - Real.sqrt a * Real.sqrt b := by rw [h_sqrt_mul]
      _ = (Real.sqrt a ^ 2 + Real.sqrt b ^ 2) / 2 - Real.sqrt a * Real.sqrt b := by
        rw [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
      _ = ((Real.sqrt a - Real.sqrt b)^2) / 2 := by ring
  
  rw [h_identity]
  
  -- Helper: factorization of a - b
  -- Proving the reverse direction to avoid rewriting issues with Real.sqrt
  have h_diff_factor_rev : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    calc
      (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = (Real.sqrt a)^2 - (Real.sqrt b)^2 := by ring
      _ = a - b := by
        rw [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
  
  have h_diff_factor : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    rw [h_diff_factor_rev.symm]
  
  -- Helper: factorization of (a - b)^2
  have h_diff_sq_factor_rev : (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 = (a - b)^2 := by
    calc
      (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b))^2 := by ring
      _ = (a - b)^2 := by rw [h_diff_factor_rev]
  
  -- Case analysis
  by_cases h_eq : a = b
  · subst h_eq
    simp [h_identity]
    <;> norm_num
    <;> linarith
  
  have h_lt : b < a := lt_of_le_of_ne h₁ (by intro h; apply h_eq; exact h.symm)
  have h_sqrt_lt : Real.sqrt b < Real.sqrt a := Real.sqrt_lt_sqrt (le_of_lt hb) h_lt
  have h_diff_pos : 0 < Real.sqrt a - Real.sqrt b := sub_pos.mpr h_sqrt_lt
  have h_diff_sq_pos : 0 < (Real.sqrt a - Real.sqrt b)^2 := sq_pos_of_pos h_diff_pos
  
  -- Target: 4 * b ≤ (Real.sqrt a + Real.sqrt b)^2
  have h_target : 4 * b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
    have h_sum_sq : (Real.sqrt a + Real.sqrt b)^2 = a + b + 2 * Real.sqrt a * Real.sqrt b := by
      ring_nf
      rw [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
      <;> ring
    rw [h_sum_sq]
    have h_sqrt_a_ge_sqrt_b : Real.sqrt a ≥ Real.sqrt b := Real.sqrt_le_sqrt h₁
    have h_prod : Real.sqrt a * Real.sqrt b ≥ Real.sqrt b * Real.sqrt b := by gcongr
    rw [Real.mul_self_sqrt (le_of_lt hb)] at h_prod
    have h_ab_ge_b : Real.sqrt a * Real.sqrt b ≥ b := by linarith
    have h_a_plus_b_ge_2b : a + b ≥ 2 * b := by linarith
    nlinarith [h_ab_ge_b, h_a_plus_b_ge_2b]
  
  -- Main Inequality: 4 * b * (Real.sqrt a - Real.sqrt b)^2 ≤ (a - b)^2
  have h_main : 4 * b * (Real.sqrt a - Real.sqrt b)^2 ≤ (a - b)^2 := by
    have h_nonneg : 0 ≤ (Real.sqrt a - Real.sqrt b)^2 := sq_nonneg _
    have h_part : 4 * b * (Real.sqrt a - Real.sqrt b)^2 ≤ (Real.sqrt a + Real.sqrt b)^2 * (Real.sqrt a - Real.sqrt b)^2 := by
      exact mul_le_mul_of_nonneg_right h_target h_nonneg
    
    calc
      4 * b * (Real.sqrt a - Real.sqrt b)^2 ≤ (Real.sqrt a + Real.sqrt b)^2 * (Real.sqrt a - Real.sqrt b)^2 := h_part
      _ = (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 := by ring
      _ = (a - b)^2 := by rw [h_diff_sq_factor_rev.symm]
  
  -- Final step: divide by 8*b
  have h_denom_pos : 0 < 8 * b := by positivity
  have h_goal : (Real.sqrt a - Real.sqrt b)^2 / 2 ≤ (a - b)^2 / (8 * b) := by
    calc
      (Real.sqrt a - Real.sqrt b)^2 / 2 = (4 * b * (Real.sqrt a - Real.sqrt b)^2) / (8 * b) := by
        field_simp [ne_of_gt h_denom_pos]
        <;> ring
      _ ≤ (a - b)^2 / (8 * b) := by
        have h_inv_pos : 0 < (8 * b)⁻¹ := inv_pos.mpr h_denom_pos
        rw [div_eq_mul_inv]
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right
        · exact h_main
        · exact le_of_lt h_inv_pos
  
  exact h_goal
