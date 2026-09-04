import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Coercions to ℝ
  have hx : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hy : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hz : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  
  -- Logarithms of bases are positive
  have h_log_x_pos : Real.log (x : ℝ) > 0 := Real.log_pos hx
  have h_log_y_pos : Real.log (y : ℝ) > 0 := Real.log_pos hy
  have h_log_z_pos : Real.log (z : ℝ) > 0 := Real.log_pos hz
  
  -- Show log w is positive (hence w > 1)
  have h_log_w_pos : Real.log (w : ℝ) > 0 := by
    have h_log_w_eq : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
      have h_div : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := h0
      have h_log_x_ne : Real.log (x : ℝ) ≠ 0 := ne_of_gt h_log_x_pos
      field_simp [h_log_x_ne] at h_div
      linarith
    rw [h_log_w_eq]
    linarith
  
  have h_log_w_ne_zero : Real.log (w : ℝ) ≠ 0 := ne_of_gt h_log_w_pos
  
  -- Properties of log(x*y*z)
  have h_log_prod : Real.log ((x * y * z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h_xy : Real.log ((x * y : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) := by
      apply Real.log_mul
      · positivity
      · positivity
    have h_xyz : Real.log ((x * y * z : ℝ)) = Real.log (((x * y : ℝ) * z)) := by ring_nf
    rw [h_xyz]
    have h_xyz_log : Real.log (((x * y : ℝ) * z)) = Real.log (x * y : ℝ) + Real.log (z : ℝ) := by
      apply Real.log_mul
      · positivity
      · positivity
    rw [h_xyz_log]
    rw [h_xy]
    <;> ring
  
  -- Extract log w relations
  have h_log_w_eq_24_log_x : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    have h_div : Real.log (w : ℝ) / Real.log (x : ℝ) = 24 := h0
    have h_log_x_ne : Real.log (x : ℝ) ≠ 0 := ne_of_gt h_log_x_pos
    field_simp [h_log_x_ne] at h_div
    linarith
  
  have h_log_w_eq_40_log_y : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have h_div : Real.log (w : ℝ) / Real.log (y : ℝ) = 40 := h1
    have h_log_y_ne : Real.log (y : ℝ) ≠ 0 := ne_of_gt h_log_y_pos
    field_simp [h_log_y_ne] at h_div
    linarith
  
  have h_log_w_eq_12_log_xyz : Real.log (w : ℝ) = 12 * Real.log ((x * y * z : ℝ)) := by
    have h_div : Real.log (w : ℝ) / Real.log ((x * y * z : ℝ)) = 12 := h2
    have h_log_xyz_ne : Real.log ((x * y * z : ℝ)) ≠ 0 := by
      have h_log_xyz_pos : Real.log ((x * y * z : ℝ)) > 0 := by
        have h_pos : (x * y * z : ℝ) > 1 := by
          calc
            (x * y * z : ℝ) = (x : ℝ) * (y : ℝ) * (z : ℝ) := by norm_cast
            _ > 1 * 1 * 1 := by gcongr <;> assumption
            _ = 1 := by norm_num
        exact Real.log_pos h_pos
      linarith
    field_simp [h_log_xyz_ne] at h_div
    linarith
  
  -- Combine to solve for log z
  have h_sum_logs : Real.log (w : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
    rw [h_log_w_eq_12_log_xyz, h_log_prod]
    <;> ring
  
  -- Substitute log x and log y
  have h_log_x_val : Real.log (x : ℝ) = Real.log (w : ℝ) / 24 := by
    have h_eq : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := h_log_w_eq_24_log_x
    have h_log_w_ne : Real.log (w : ℝ) ≠ 0 := h_log_w_ne_zero
    field_simp [h_log_w_ne] at h_eq ⊢
    linarith
  
  have h_log_y_val : Real.log (y : ℝ) = Real.log (w : ℝ) / 40 := by
    have h_eq : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := h_log_w_eq_40_log_y
    have h_log_w_ne : Real.log (w : ℝ) ≠ 0 := h_log_w_ne_zero
    field_simp [h_log_w_ne] at h_eq ⊢
    linarith
  
  have h_substituted : Real.log (w : ℝ) = 12 * (Real.log (w : ℝ) / 24 + Real.log (w : ℝ) / 40 + Real.log (z : ℝ)) := by
    rw [h_log_x_val, h_log_y_val] at h_sum_logs
    exact h_sum_logs
  
  -- Arithmetic simplification
  have h_arith : Real.log (w : ℝ) = (1 / 2 + 3 / 10) * Real.log (w : ℝ) + 12 * Real.log (z : ℝ) := by
    ring_nf at h_substituted ⊢
    linarith
  
  have h_diff : (1 - (1 / 2 + 3 / 10)) * Real.log (w : ℝ) = 12 * Real.log (z : ℝ) := by
    linarith
  
  have h_const : (1 : ℝ) - (1 / 2 + 3 / 10) = 1 / 5 := by norm_num
  have h_scaled : (1 / 5) * Real.log (w : ℝ) = 12 * Real.log (z : ℝ) := by
    rw [h_const] at h_diff
    exact h_diff
  
  have h_log_z_val : Real.log (z : ℝ) = (1 / 60) * Real.log (w : ℝ) := by
    field_simp at h_scaled ⊢
    linarith
  
  have h_target : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have h_log_z_ne : Real.log (z : ℝ) ≠ 0 := ne_of_gt h_log_z_pos
    have h_log_w_ne : Real.log (w : ℝ) ≠ 0 := h_log_w_ne_zero
    calc
      Real.log (w : ℝ) / Real.log (z : ℝ) = Real.log (w : ℝ) / ((1 / 60) * Real.log (w : ℝ)) := by rw [h_log_z_val]
      _ = 1 / (1 / 60) := by
        field_simp [h_log_w_ne]
        <;> ring
      _ = 60 := by norm_num
  
  exact h_target
