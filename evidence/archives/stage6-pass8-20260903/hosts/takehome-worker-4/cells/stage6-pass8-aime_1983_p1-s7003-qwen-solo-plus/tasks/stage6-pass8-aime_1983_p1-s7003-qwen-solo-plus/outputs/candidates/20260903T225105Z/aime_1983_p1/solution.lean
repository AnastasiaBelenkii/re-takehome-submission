import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  have hx : 1 < x := ht.1
  have hy : 1 < y := ht.2.1
  have hz : 1 < z := ht.2.2
  
  have hx_pos : (x : ℝ) > 1 := by exact_mod_cast hx
  have hy_pos : (y : ℝ) > 1 := by exact_mod_cast hy
  have hz_pos : (z : ℝ) > 1 := by exact_mod_cast hz
  
  have hx_log_pos : Real.log (x : ℝ) > 0 := Real.log_pos hx_pos
  have hy_log_pos : Real.log (y : ℝ) > 0 := Real.log_pos hy_pos
  have hz_log_pos : Real.log (z : ℝ) > 0 := Real.log_pos hz_pos
  
  have hx_log_ne_zero : Real.log (x : ℝ) ≠ 0 := ne_of_gt hx_log_pos
  have hy_log_ne_zero : Real.log (y : ℝ) ≠ 0 := ne_of_gt hy_log_pos
  have hz_log_ne_zero : Real.log (z : ℝ) ≠ 0 := ne_of_gt hz_log_pos
  
  have h0_eq : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    have : Real.log (x : ℝ) ≠ 0 := hx_log_ne_zero
    field_simp [this] at h0 ⊢
    <;> ring_nf at h0 ⊢ <;> linarith
  
  have h1_eq : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have : Real.log (y : ℝ) ≠ 0 := hy_log_ne_zero
    field_simp [this] at h1 ⊢
    <;> ring_nf at h1 ⊢ <;> linarith
  
  have h_prod_log : Real.log ((x * y * z) : ℝ) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have hxy_pos : (x * y : ℝ) > 0 := by positivity
    have hxyz_pos : (x * y * z : ℝ) > 0 := by positivity
    calc
      Real.log ((x * y * z) : ℝ) = Real.log (((x * y) * z) : ℝ) := by ring_nf
      _ = Real.log ((x * y) : ℝ) + Real.log (z : ℝ) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = (Real.log (x : ℝ) + Real.log (y : ℝ)) + Real.log (z : ℝ) := by rw [Real.log_mul (by positivity) (by positivity)]
      _ = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by ring
  
  have h2_eq : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    have : Real.log ((x * y * z) : ℝ) ≠ 0 := by
      rw [h_prod_log]
      intro h
      have : Real.log (x : ℝ) > 0 := hx_log_pos
      have : Real.log (y : ℝ) > 0 := hy_log_pos
      have : Real.log (z : ℝ) > 0 := hz_log_pos
      linarith
    field_simp [this] at h2 ⊢
    <;> rw [h_prod_log] at h2
    <;> ring_nf at h2 ⊢
    <;> linarith
  
  have h_xy : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by
    linarith [h0_eq, h1_eq]
  
  have h_xy_rel : Real.log (x : ℝ) = (5/3 : ℝ) * Real.log (y : ℝ) := by
    have : Real.log (y : ℝ) ≠ 0 := hy_log_ne_zero
    field_simp [this] at h_xy ⊢
    <;> ring_nf at h_xy ⊢
    <;> linarith
  
  have h_w_y_z : Real.log (w : ℝ) = 12 * ((5/3 : ℝ) * Real.log (y : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    rw [h_xy_rel] at h2_eq
    exact h2_eq
  
  have h_w_y_z_eq : 40 * Real.log (y : ℝ) = 12 * ((5/3 : ℝ) * Real.log (y : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    linarith [h1_eq, h_w_y_z]
  
  have h_y_z : 8 * Real.log (y : ℝ) = 12 * Real.log (z : ℝ) := by
    ring_nf at h_w_y_z_eq ⊢
    linarith
  
  have h_y_z_rel : Real.log (y : ℝ) = (3/2 : ℝ) * Real.log (z : ℝ) := by
    have : Real.log (z : ℝ) ≠ 0 := hz_log_ne_zero
    field_simp [this] at h_y_z ⊢
    <;> ring_nf at h_y_z ⊢
    <;> linarith
  
  have h_w_z : Real.log (w : ℝ) = 60 * Real.log (z : ℝ) := by
    calc
      Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by rw [h1_eq]
      _ = 40 * ((3/2 : ℝ) * Real.log (z : ℝ)) := by rw [h_y_z_rel]
      _ = 60 * Real.log (z : ℝ) := by ring
  
  have h_final : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have : Real.log (z : ℝ) ≠ 0 := hz_log_ne_zero
    field_simp [this] at h_w_z ⊢
    <;> linarith
  
  exact h_final
