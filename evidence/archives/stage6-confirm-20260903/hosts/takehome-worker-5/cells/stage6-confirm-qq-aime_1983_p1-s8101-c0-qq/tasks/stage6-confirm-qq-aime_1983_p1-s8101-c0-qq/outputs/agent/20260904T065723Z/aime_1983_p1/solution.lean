import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast inequalities to Reals
  have hx_gt_one : (1 : ℝ) < x := by exact_mod_cast ht.1
  have hy_gt_one : (1 : ℝ) < y := by exact_mod_cast ht.2.1
  have hz_gt_one : (1 : ℝ) < z := by exact_mod_cast ht.2.2
  
  -- Positivity of logs
  have hx_log_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hy_log_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hz_log_pos : 0 < Real.log z := Real.log_pos hz_gt_one
  
  -- Derive log(w) expressions from h0, h1, h2
  have h_log_w_eq_24_log_x : Real.log w = 24 * Real.log x := by
    have h : Real.log w / Real.log x = 24 := h0
    field_simp [hx_log_pos.ne'] at h ⊢
    linarith
  
  have h_log_w_eq_40_log_y : Real.log w = 40 * Real.log y := by
    have h : Real.log w / Real.log y = 40 := h1
    field_simp [hy_log_pos.ne'] at h ⊢
    linarith
    
  -- Establish 1 < x * y * z in Nat first to avoid Real arithmetic issues
  have h_xy : 1 < x * y := by
    have h_y_ge_one : 1 ≤ y := by linarith [ht.2.1]
    have h_x_gt_one : 1 < x := ht.1
    calc
      1 < x := h_x_gt_one
      _ ≤ x * y := by
        have h_y_pos : 0 < y := by linarith
        nlinarith
  
  have h_xyz : 1 < x * y * z := by
    have h_z_ge_one : 1 ≤ z := by linarith [ht.2.2]
    have h_xy_gt_one : 1 < x * y := h_xy
    calc
      1 < x * y := h_xy_gt_one
      _ ≤ x * y * z := by
        have h_z_pos : 0 < z := by linarith
        nlinarith
  
  have h_xyz_gt_one : (1 : ℝ) < x * y * z := by exact_mod_cast h_xyz
  
  have h_log_w_eq_12_log_xyz : Real.log w = 12 * Real.log (x * y * z) := by
    have h : Real.log w / Real.log (x * y * z) = 12 := h2
    have h_denom_ne_zero : Real.log (x * y * z) ≠ 0 := by
      have h_log_pos : 0 < Real.log (x * y * z) := Real.log_pos h_xyz_gt_one
      exact h_log_pos.ne'
    field_simp [h_denom_ne_zero] at h ⊢
    linarith

  -- Expand log(x * y * z)
  have h_log_xyz : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    calc
      Real.log (x * y * z) = Real.log ((x * y) * z) := by ring_nf
      _ = Real.log (x * y) + Real.log z := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log x + Real.log y) + Real.log z := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log x + Real.log y + Real.log z := by ring

  -- Substitute back into h_log_w_eq_12_log_xyz
  have h_log_w_eq_12_sum_logs : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    rw [h_log_xyz] at h_log_w_eq_12_log_xyz
    exact h_log_w_eq_12_log_xyz

  -- Solve the system
  have h_log_x_eq_sum : Real.log x = Real.log y + Real.log z := by
    have h_eq : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
      linarith [h_log_w_eq_24_log_x, h_log_w_eq_12_sum_logs]
    linarith

  have h_40_log_y_eq_24_log_x : 40 * Real.log y = 24 * Real.log x := by
    linarith [h_log_w_eq_40_log_y, h_log_w_eq_24_log_x]
  
  have h_16_log_y_eq_24_log_z : 16 * Real.log y = 24 * Real.log z := by
    rw [h_log_x_eq_sum] at h_40_log_y_eq_24_log_x
    linarith
  
  have h_2_log_y_eq_3_log_z : 2 * Real.log y = 3 * Real.log z := by
    apply mul_left_cancel₀ (show (8 : ℝ) ≠ 0 by norm_num)
    linarith
  
  have h_log_y_eq_3_over_2_log_z : Real.log y = (3/2 : ℝ) * Real.log z := by
    field_simp at h_2_log_y_eq_3_log_z ⊢
    linarith
  
  -- Calculate log w / log z
  have h_log_w_eq_60_log_z : Real.log w = 60 * Real.log z := by
    calc
      Real.log w = 40 * Real.log y := by rw [h_log_w_eq_40_log_y]
      _ = 40 * ((3/2 : ℝ) * Real.log z) := by rw [h_log_y_eq_3_over_2_log_z]
      _ = 60 * Real.log z := by ring

  -- Final result
  have h_final : Real.log w / Real.log z = 60 := by
    field_simp [hz_log_pos.ne'] at h_log_w_eq_60_log_z ⊢
    linarith
  
  exact h_final
