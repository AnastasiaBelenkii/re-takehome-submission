import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast inequalities to Reals
  have hx_gt_1 : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hy_gt_1 : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hz_gt_1 : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  
  -- Positivity
  have hx_pos : 0 < (x : ℝ) := by linarith
  have hy_pos : 0 < (y : ℝ) := by linarith
  have hz_pos : 0 < (z : ℝ) := by linarith
  
  -- Non-zero logs for x, y, z
  have hx_log_ne_zero : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos (ne_of_gt hx_gt_1)
  have hy_log_ne_zero : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy_pos (ne_of_gt hy_gt_1)
  have hz_log_ne_zero : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hz_pos (ne_of_gt hz_gt_1)
  
  -- Product positivity and log non-zero
  have hxy_pos : 0 < (x * y : ℝ) := mul_pos hx_pos hy_pos
  have hxyz_pos : 0 < (x * y * z : ℝ) := mul_pos (mul_pos hx_pos hy_pos) hz_pos
  have hxyz_gt_1 : (x * y * z : ℝ) > 1 := by
    calc
      (x * y * z : ℝ) > 1 * 1 * 1 := by gcongr <;> assumption
      _ = 1 := by norm_num
  have hxyz_log_ne_zero : Real.log (x * y * z : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hxyz_pos (ne_of_gt hxyz_gt_1)
  
  -- Convert equations
  have h_log_w_eq_24_log_x : Real.log w = 24 * Real.log x := by
    field_simp [hx_log_ne_zero] at h0 ⊢
    linarith
  
  have h_log_w_eq_40_log_y : Real.log w = 40 * Real.log y := by
    field_simp [hy_log_ne_zero] at h1 ⊢
    linarith
  
  have h_log_prod_xyz : Real.log (x * y * z : ℝ) = Real.log x + Real.log y + Real.log z := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  
  have h_log_w_eq_12_log_xyz : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    field_simp [hxyz_log_ne_zero] at h2 ⊢
    rw [h_log_prod_xyz] at h2
    linarith
  
  -- Main derivation
  have h_24_log_x_eq_40_log_y : 24 * Real.log x = 40 * Real.log y := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_40_log_y]
  
  have h_24_log_x_eq_12_sum : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_12_log_xyz]
  
  have h_log_x_eq_log_y_add_log_z : Real.log x = Real.log y + Real.log z := by
    linarith [h_24_log_x_eq_12_sum]
  
  have h_log_y_eq_3_5_log_x : Real.log y = (3/5 : ℝ) * Real.log x := by
    have h_ratio : 24 * Real.log x = 40 * Real.log y := h_24_log_x_eq_40_log_y
    field_simp [hx_log_ne_zero] at h_ratio ⊢
    linarith
  
  have h_log_z_eq_2_5_log_x : Real.log z = (2/5 : ℝ) * Real.log x := by
    have h_sub : Real.log z = Real.log x - Real.log y := by linarith [h_log_x_eq_log_y_add_log_z]
    rw [h_sub, h_log_y_eq_3_5_log_x]
    ring_nf
    <;> field_simp [hx_log_ne_zero]
    <;> linarith
  
  have h_main : Real.log w / Real.log z = 60 := by
    rw [h_log_w_eq_24_log_x, h_log_z_eq_2_5_log_x]
    field_simp [hx_log_ne_zero, hz_log_ne_zero]
    ring_nf
    <;> norm_num
    <;> linarith
  
  exact h_main
