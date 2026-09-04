import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx_gt_one : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hy_gt_one : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hz_gt_one : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  
  have hx_log_ne_zero : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have hy_log_ne_zero : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  have hz_log_ne_zero : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  
  have h_log_w_eq_24_log_x : Real.log w = 24 * Real.log x := by
    have h0' : Real.log x ≠ 0 := hx_log_ne_zero
    field_simp [h0'] at h0 ⊢
    linarith
  
  have h_log_w_eq_40_log_y : Real.log w = 40 * Real.log y := by
    have h1' : Real.log y ≠ 0 := hy_log_ne_zero
    field_simp [h1'] at h1 ⊢
    linarith
  
  have h_log_xyz : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    have hxy_pos : 0 < (x * y : ℝ) := by positivity
    have hxyz_pos : 0 < (x * y * z : ℝ) := by positivity
    calc
      Real.log (x * y * z) = Real.log ((x * y) * z) := by ring_nf
      _ = Real.log (x * y) + Real.log z := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log x + Real.log y) + Real.log z := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log x + Real.log y + Real.log z := by ring
  
  have h_log_xyz_ne_zero : Real.log (x * y * z) ≠ 0 := by
    have h_prod_gt_one : (x * y * z : ℝ) > 1 := by
      have : (x : ℝ) > 1 := hx_gt_one
      have : (y : ℝ) > 1 := hy_gt_one
      have : (z : ℝ) > 1 := hz_gt_one
      calc
        (x * y * z : ℝ) > 1 * 1 * 1 := by gcongr <;> assumption
        _ = 1 := by norm_num
    exact Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  
  have h_log_w_eq_12_log_xyz : Real.log w = 12 * Real.log (x * y * z) := by
    have h2' : Real.log (x * y * z) ≠ 0 := h_log_xyz_ne_zero
    field_simp [h2'] at h2 ⊢
    linarith
  
  have h_log_w_eq_12_sum_logs : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    rw [h_log_w_eq_12_log_xyz, h_log_xyz]
    <;> ring
  
  have h_combined : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_12_sum_logs]
  
  have h_log_x_eq_sum_yz : Real.log x = Real.log y + Real.log z := by
    linarith
  
  have h_xy_rel : 24 * Real.log x = 40 * Real.log y := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_40_log_y]
  
  have h_log_y_in_terms_of_x : Real.log y = (3/5 : ℝ) * Real.log x := by
    have h_log_x_ne_zero : Real.log x ≠ 0 := hx_log_ne_zero
    field_simp [h_log_x_ne_zero] at h_xy_rel ⊢
    linarith
  
  have h_log_z_in_terms_of_x : Real.log z = (2/5 : ℝ) * Real.log x := by
    rw [h_log_y_in_terms_of_x] at h_log_x_eq_sum_yz
    linarith
  
  have h_main : Real.log w / Real.log z = 60 := by
    calc
      Real.log w / Real.log z = (24 * Real.log x) / Real.log z := by rw [h_log_w_eq_24_log_x]
      _ = (24 * Real.log x) / ((2/5 : ℝ) * Real.log x) := by rw [h_log_z_in_terms_of_x]
      _ = 24 / (2/5 : ℝ) := by
        field_simp [hx_log_ne_zero]
        <;> ring_nf
        <;> field_simp [hx_log_ne_zero]
        <;> linarith
      _ = 60 := by norm_num
  
  exact h_main
