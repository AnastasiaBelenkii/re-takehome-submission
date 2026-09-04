import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx_gt_one : 1 < x := ht.1
  have hy_gt_one : 1 < y := ht.2.1
  have hz_gt_one : 1 < z := ht.2.2
  
  -- Logs of bases are positive
  have hx_log_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx_gt_one)
  have hy_log_pos : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy_gt_one)
  have hz_log_pos : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz_gt_one)
  
  -- Log of product is positive
  have hxyz_gt_one : 1 < (x * y * z : ℕ) := by
    have : 1 < x * y := by nlinarith [hx_gt_one, hy_gt_one]
    nlinarith [this, hz_gt_one]
  have hxyz_log_pos : 0 < Real.log ((x * y * z) : ℝ) := Real.log_pos (by exact_mod_cast hxyz_gt_one)
  
  -- Express logs of bases in terms of log w
  have h_log_x : Real.log (x : ℝ) = Real.log (w : ℝ) / 24 := by
    have h0' : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by simpa using h0
    field_simp [hx_log_pos.ne'] at h0' ⊢
    linarith
  
  have h_log_y : Real.log (y : ℝ) = Real.log (w : ℝ) / 40 := by
    have h1' : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := by simpa using h1
    field_simp [hy_log_pos.ne'] at h1' ⊢
    linarith
  
  have h_log_xyz : Real.log ((x * y * z) : ℝ) = Real.log (w : ℝ) / 12 := by
    have h2' : Real.log (w : ℝ) / Real.log ((x * y * z) : ℝ) = 12 := by simpa using h2
    field_simp [hxyz_log_pos.ne'] at h2' ⊢
    linarith
  
  -- Log sum property for three numbers
  have h_log_sum : Real.log ((x * y * z) : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h_xy_pos : 0 < (x : ℝ) := by positivity
    have h_yz_pos : 0 < (y : ℝ) := by positivity
    have h_z_pos : 0 < (z : ℝ) := by positivity
    have h_xyz_pos : 0 < (x : ℝ) * (y : ℝ) * (z : ℝ) := by positivity
    calc
      Real.log ((x * y * z) : ℝ) = Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by norm_cast
      _ = Real.log (((x : ℝ) * (y : ℝ)) * (z : ℝ)) := by ring_nf
      _ = Real.log ((x : ℝ) * (y : ℝ)) + Real.log (z : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log (x : ℝ) + Real.log (y : ℝ)) + Real.log (z : ℝ) := by
        rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by ring
  
  -- Solve for log z
  have h_log_z_calc : Real.log (z : ℝ) = Real.log (w : ℝ) / 60 := by
    rw [h_log_sum] at h_log_xyz
    rw [h_log_x, h_log_y] at h_log_xyz
    field_simp [hx_log_pos.ne', hy_log_pos.ne', hz_log_pos.ne', hxyz_log_pos.ne'] at h_log_xyz ⊢
    linarith
  
  -- Final calculation
  have h_w_log_ne_zero : Real.log (w : ℝ) ≠ 0 := by
    intro h
    have h0' : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := by simpa using h0
    rw [h] at h0'
    norm_num at h0'
  
  have h_z_log_ne_zero : Real.log (z : ℝ) ≠ 0 := hz_log_pos.ne'
  
  have h_final : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    field_simp [hz_log_pos.ne', h_w_log_ne_zero, h_z_log_ne_zero] at h_log_z_calc ⊢
    linarith
  
  exact h_final
