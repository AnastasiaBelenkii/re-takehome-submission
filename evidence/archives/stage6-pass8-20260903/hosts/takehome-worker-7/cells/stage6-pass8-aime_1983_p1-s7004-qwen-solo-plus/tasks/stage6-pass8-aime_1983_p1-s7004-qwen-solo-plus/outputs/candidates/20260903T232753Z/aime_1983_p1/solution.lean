import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : (1 : ℝ) < x := by exact_mod_cast ht.1
  have hy : (1 : ℝ) < y := by exact_mod_cast ht.2.1
  have hz : (1 : ℝ) < z := by exact_mod_cast ht.2.2
  
  have hx_log_pos : 0 < Real.log x := Real.log_pos hx
  have hy_log_pos : 0 < Real.log y := Real.log_pos hy
  have hz_log_pos : 0 < Real.log z := Real.log_pos hz
  
  have hx_log_ne_zero : Real.log x ≠ 0 := by linarith
  have hy_log_ne_zero : Real.log y ≠ 0 := by linarith
  have hz_log_ne_zero : Real.log z ≠ 0 := by linarith
  
  have h_w_eq_x : Real.log w = 24 * Real.log x := by
    have h : Real.log x ≠ 0 := hx_log_ne_zero
    field_simp [h] at h0 ⊢
    <;> linarith
  
  have h_w_eq_y : Real.log w = 40 * Real.log y := by
    have h : Real.log y ≠ 0 := hy_log_ne_zero
    field_simp [h] at h1 ⊢
    <;> linarith

  have h_xyz_log : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    have hxy_ne_zero : (x * y : ℝ) ≠ 0 := by positivity
    have hz_ne_zero : (z : ℝ) ≠ 0 := by positivity
    calc
      Real.log (x * y * z) = Real.log ((x * y) * z) := by ring_nf
      _ = Real.log (x * y) + Real.log z := by
        rw [Real.log_mul] <;> positivity
      _ = (Real.log x + Real.log y) + Real.log z := by
        rw [Real.log_mul] <;> positivity
      _ = Real.log x + Real.log y + Real.log z := by ring

  have h_w_eq_xyz : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h : Real.log (x * y * z) ≠ 0 := by
      rw [h_xyz_log]
      linarith [hx_log_pos, hy_log_pos, hz_log_pos]
    field_simp [h] at h2 ⊢
    <;> rw [h_xyz_log] at h2
    <;> ring_nf at h2 ⊢
    <;> linarith

  have h_xy_z_rel : Real.log x = Real.log y + Real.log z := by
    have : Real.log w = 24 * Real.log x := h_w_eq_x
    have : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := h_w_eq_xyz
    have : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
    have : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by linarith
    linarith

  have h_z_def : Real.log z = Real.log x - Real.log y := by
    linarith [h_xy_z_rel]

  have h_x_y_rel : Real.log x = (5/3 : ℝ) * Real.log y := by
    have : Real.log w = 24 * Real.log x := h_w_eq_x
    have : Real.log w = 40 * Real.log y := h_w_eq_y
    have : 24 * Real.log x = 40 * Real.log y := by linarith
    have : Real.log x ≠ 0 := hx_log_ne_zero
    field_simp [this] at *
    <;> ring_nf at *
    <;> linarith

  have h_z_val_calc : Real.log z = (2/3 : ℝ) * Real.log y := by
    rw [h_z_def, h_x_y_rel]
    ring_nf
    <;> field_simp
    <;> ring_nf

  have h_final : Real.log w / Real.log z = 60 := by
    have h_w_val : Real.log w = 40 * Real.log y := h_w_eq_y
    calc
      Real.log w / Real.log z = (40 * Real.log y) / ((2/3 : ℝ) * Real.log y) := by
        rw [h_w_val, h_z_val_calc]
      _ = 40 / (2/3 : ℝ) := by
        have h_y_log_ne_zero : Real.log y ≠ 0 := hy_log_ne_zero
        field_simp [h_y_log_ne_zero]
        <;> ring_nf
      _ = 60 := by norm_num
      
  exact h_final
