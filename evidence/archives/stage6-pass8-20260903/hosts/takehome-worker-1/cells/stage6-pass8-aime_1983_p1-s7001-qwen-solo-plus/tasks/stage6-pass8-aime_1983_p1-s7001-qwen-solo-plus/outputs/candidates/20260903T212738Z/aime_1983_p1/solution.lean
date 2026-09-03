import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast inequalities to ℝ for logarithm domain
  have hx_gt_one : (1 : ℝ) < x := by exact_mod_cast ht.1
  have hy_gt_one : (1 : ℝ) < y := by exact_mod_cast ht.2.1
  have hz_gt_one : (1 : ℝ) < z := by exact_mod_cast ht.2.2
  
  -- Logarithms of bases are positive (needed for division)
  have hx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hy_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hz_pos : 0 < Real.log z := Real.log_pos hz_gt_one
  
  -- From h0 and h1, express log(w) in terms of log(x) and log(y)
  have h_log_w_eq_24_log_x : Real.log w = 24 * Real.log x := by
    have h0' : Real.log w / Real.log x = 24 := h0
    field_simp [hx_pos.ne'] at h0' ⊢
    linarith
  
  have h_log_w_eq_40_log_y : Real.log w = 40 * Real.log y := by
    have h1' : Real.log w / Real.log y = 40 := h1
    field_simp [hy_pos.ne'] at h1' ⊢
    linarith
  
  -- From h2, expand log(x*y*z) using log product rule
  -- Note: Real.log (x * y * z) in h2 is Real.log (↑(x * y * z))
  -- We need to equate this to Real.log (↑x * ↑y * ↑z)
  have h_log_prod : Real.log (↑x * ↑y * ↑z) = Real.log x + Real.log y + Real.log z := by
    have h_xy_pos : 0 < (↑x * ↑y : ℝ) := by positivity
    have h_xyz_pos : 0 < (↑x * ↑y * ↑z : ℝ) := by positivity
    calc
      Real.log (↑x * ↑y * ↑z) = Real.log ((↑x * ↑y : ℝ) * ↑z) := by ring_nf
      _ = Real.log (↑x * ↑y : ℝ) + Real.log ↑z := by
        apply Real.log_mul
        · positivity
        · positivity
      _ = (Real.log ↑x + Real.log ↑y) + Real.log ↑z := by
        rw [Real.log_mul] <;> positivity
  
  -- Use h2 to get equation relating log(x), log(y), log(z)
  have h2_expanded : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h2' : Real.log w / Real.log (x * y * z) = 12 := h2
    have h_denom_eq : Real.log (x * y * z) = Real.log (↑x * ↑y * ↑z) := by
      congr
      <;> norm_cast
      <;> ring_nf
    rw [h_denom_eq] at h2'
    have h_denom_ne_zero : Real.log (↑x * ↑y * ↑z) ≠ 0 := by
      rw [h_log_prod]
      intro h_eq
      have h_sum : Real.log x + Real.log y + Real.log z = 0 := h_eq
      have h_pos : 0 < Real.log x + Real.log y + Real.log z := by
        linarith [hx_pos, hy_pos, hz_pos]
      linarith
    field_simp [h_denom_ne_zero] at h2' ⊢
    linarith
  
  -- Combine h_log_w_eq_24_log_x and h2_expanded
  have h_main_eq : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
    rw [h_log_w_eq_24_log_x] at h2_expanded
    linarith
  
  -- Simplify to get relationship between log(x), log(y), log(z)
  have h_simplified : Real.log x = Real.log y + Real.log z := by
    have h3 : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := h_main_eq
    linarith
  
  -- Express log(z) in terms of log(x) and log(y)
  have h_log_z_in_terms : Real.log z = Real.log x - Real.log y := by linarith
  
  -- From h_log_w_eq_24_log_x and h_log_w_eq_40_log_y, relate log(x) and log(y)
  have h_xy_relation : 24 * Real.log x = 40 * Real.log y := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_40_log_y]
  
  -- Solve for log(y) in terms of log(x)
  have h_log_y_in_terms : Real.log y = (3/5 : ℝ) * Real.log x := by
    have h4 : 24 * Real.log x = 40 * Real.log y := h_xy_relation
    field_simp at h4 ⊢
    <;> ring_nf at h4 ⊢ <;> linarith
  
  -- Substitute to get log(z) in terms of log(x)
  have h_log_z_final : Real.log z = (2/5 : ℝ) * Real.log x := by
    rw [h_log_z_in_terms, h_log_y_in_terms]
    ring_nf
    <;> field_simp
    <;> ring_nf
  
  -- Now compute log(w)/log(z)
  have h_result : Real.log w / Real.log z = 60 := by
    rw [h_log_w_eq_24_log_x, h_log_z_final]
    field_simp [hz_pos.ne', hx_pos.ne']
    <;> ring_nf
    <;> norm_num
  
  exact h_result
