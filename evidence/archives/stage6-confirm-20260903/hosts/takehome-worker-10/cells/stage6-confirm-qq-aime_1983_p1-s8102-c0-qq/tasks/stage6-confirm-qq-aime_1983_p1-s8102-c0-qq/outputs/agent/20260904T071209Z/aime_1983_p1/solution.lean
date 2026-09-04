import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx_gt_one : (1 : ℝ) < (x : ℝ) := by norm_cast; exact ht.1
  have hy_gt_one : (1 : ℝ) < (y : ℝ) := by norm_cast; exact ht.2.1
  have hz_gt_one : (1 : ℝ) < (z : ℝ) := by norm_cast; exact ht.2.2
  
  have h_log_x_pos : 0 < Real.log (x : ℝ) := Real.log_pos hx_gt_one
  have h_log_y_pos : 0 < Real.log (y : ℝ) := Real.log_pos hy_gt_one
  have h_log_z_pos : 0 < Real.log (z : ℝ) := Real.log_pos hz_gt_one
  
  have h_log_x_ne_zero : Real.log (x : ℝ) ≠ 0 := by linarith
  have h_log_y_ne_zero : Real.log (y : ℝ) ≠ 0 := by linarith
  have h_log_z_ne_zero : Real.log (z : ℝ) ≠ 0 := by linarith
  
  have h_log_w_pos : 0 < Real.log (w : ℝ) := by
    have : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      field_simp [h_log_x_ne_zero] at h0 ⊢
      linarith
    linarith [h_log_x_pos]
  
  have h_log_w_ne_zero : Real.log (w : ℝ) ≠ 0 := by linarith
  
  have h_log_xyz_pos : 0 < Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    have : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_mul (by positivity) (by positivity)]
      <;> ring_nf
    rw [this]
    linarith [h_log_x_pos, h_log_y_pos, h_log_z_pos]
  
  have h_log_xyz_ne_zero : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) ≠ 0 := by linarith
  
  have h0_mul : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    field_simp [h_log_x_ne_zero] at h0 ⊢
    linarith
  
  have h1_mul : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    field_simp [h_log_y_ne_zero] at h1 ⊢
    linarith
  
  have h2_mul : Real.log (w : ℝ) = 12 * Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    field_simp [h_log_xyz_ne_zero] at h2 ⊢
    linarith
  
  have h_log_xyz : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    <;> ring_nf
  
  have h2_subst : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    rw [h_log_xyz] at h2_mul
    exact h2_mul
  
  have h_xy_rel : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by
    linarith [h0_mul, h1_mul]
  
  have h_y_in_terms_of_x : Real.log (y : ℝ) = (3/5 : ℝ) * Real.log (x : ℝ) := by
    have : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := h_xy_rel
    field_simp at this ⊢
    linarith
  
  have h2_with_y : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + (3/5 : ℝ) * Real.log (x : ℝ) + Real.log (z : ℝ)) := by
    rw [h_y_in_terms_of_x] at h2_subst
    exact h2_subst
  
  have h2_with_x : 24 * Real.log (x : ℝ) = 12 * (Real.log (x : ℝ) + (3/5 : ℝ) * Real.log (x : ℝ) + Real.log (z : ℝ)) := by
    linarith [h0_mul, h2_with_y]
  
  have h_z_in_terms_of_x : Real.log (z : ℝ) = (2/5 : ℝ) * Real.log (x : ℝ) := by
    have : 24 * Real.log (x : ℝ) = 12 * (Real.log (x : ℝ) + (3/5 : ℝ) * Real.log (x : ℝ) + Real.log (z : ℝ)) := h2_with_x
    ring_nf at this ⊢
    linarith
  
  have h_final : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    rw [h0_mul, h_z_in_terms_of_x]
    field_simp [h_log_x_ne_zero, h_log_z_ne_zero]
    <;> ring_nf
    <;> norm_num
  
  exact h_final
