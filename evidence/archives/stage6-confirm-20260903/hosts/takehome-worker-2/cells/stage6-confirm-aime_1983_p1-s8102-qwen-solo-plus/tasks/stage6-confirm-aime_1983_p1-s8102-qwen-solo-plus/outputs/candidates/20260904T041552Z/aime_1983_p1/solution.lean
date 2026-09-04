import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast natural number inequalities to real numbers
  have hx_gt_one : (1 : ℝ) < x := by exact_mod_cast ht.1
  have hy_gt_one : (1 : ℝ) < y := by exact_mod_cast ht.2.1
  have hz_gt_one : (1 : ℝ) < z := by exact_mod_cast ht.2.2
  
  -- Logarithms of bases are positive
  have hx_pos : 0 < Real.log x := Real.log_pos hx_gt_one
  have hy_pos : 0 < Real.log y := Real.log_pos hy_gt_one
  have hz_pos : 0 < Real.log z := Real.log_pos hz_gt_one
  
  -- Denominators are non-zero
  have hx_log_ne_zero : Real.log x ≠ 0 := ne_of_gt hx_pos
  have hy_log_ne_zero : Real.log y ≠ 0 := ne_of_gt hy_pos
  have hz_log_ne_zero : Real.log z ≠ 0 := ne_of_gt hz_pos
  
  -- Derive log w expressions from h0 and h1
  have h_log_w_eq_24_log_x : Real.log w = 24 * Real.log x := by
    field_simp [hx_log_ne_zero] at h0 ⊢
    linarith
  
  have h_log_w_eq_40_log_y : Real.log w = 40 * Real.log y := by
    field_simp [hy_log_ne_zero] at h1 ⊢
    linarith
  
  -- Calculate log(x * y * z)
  -- We need to show x * y * z > 0 in ℝ to use Real.log_mul
  have hx_pos_real : 0 < (x : ℝ) := by linarith [hx_gt_one]
  have hy_pos_real : 0 < (y : ℝ) := by linarith [hy_gt_one]
  have hz_pos_real : 0 < (z : ℝ) := by linarith [hz_gt_one]
  
  have hxy_pos_real : 0 < (x : ℝ) * (y : ℝ) := mul_pos hx_pos_real hy_pos_real
  have hxyz_pos_real : 0 < (x : ℝ) * (y : ℝ) * (z : ℝ) := mul_pos hxy_pos_real hz_pos_real
  
  have h_log_prod : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    -- Work with the real cast explicitly to apply Real.log_mul
    have h_cast : (↑(x * y * z) : ℝ) = (↑x * ↑y * ↑z : ℝ) := by norm_cast
    -- The goal is Real.log (↑(x * y * z)). 
    -- We rewrite to Real.log (↑x * ↑y * ↑z) to facilitate splitting.
    -- Note: Depending on parsing, the goal might already be in the form Real.log (↑x * ↑y * ↑z).
    -- If it is, rw [h_cast] does nothing. If it is Real.log (↑(x * y * z)), it helps.
    -- We use calc to be explicit.
    calc
      Real.log (x * y * z) = Real.log (↑(x * y * z) : ℝ) := by simp [Real.log]
      _ = Real.log (↑x * ↑y * ↑z : ℝ) := by rw [h_cast]
      _ = Real.log ((↑x * ↑y : ℝ) * ↑z) := by ring
      _ = Real.log (↑x * ↑y : ℝ) + Real.log ↑z := by
        apply Real.log_mul
        · positivity
        · positivity
      _ = (Real.log ↑x + Real.log ↑y) + Real.log ↑z := by
        apply congr_arg (fun t => t + Real.log ↑z)
        apply Real.log_mul
        · positivity
        · positivity
      _ = Real.log x + Real.log y + Real.log z := by simp [Real.log]
  
  -- Derive log w expression from h2
  have h_log_w_eq_12_log_xyz : Real.log w = 12 * Real.log (x * y * z) := by
    have h_log_xyz_ne_zero : Real.log (x * y * z) ≠ 0 := by
      have h_log_xyz_pos : 0 < Real.log (x * y * z) := Real.log_pos (by
        have h_xyz_gt_one : (1 : ℝ) < x * y * z := by
          calc
            (1 : ℝ) < x := hx_gt_one
            _ ≤ x * y * z := by
              have hxy_ge_one : (1 : ℝ) ≤ x * y := by
                nlinarith [hx_gt_one, hy_gt_one]
              nlinarith [hxy_ge_one, hz_gt_one]
        exact_mod_cast h_xyz_gt_one)
      exact ne_of_gt h_log_xyz_pos
    field_simp [h_log_xyz_ne_zero] at h2 ⊢
    linarith
  
  -- Combine equations
  -- 24 * log x = 40 * log y => log x = (40/24) log y = (5/3) log y
  have h_xy_rel : 24 * Real.log x = 40 * Real.log y := by
    linarith [h_log_w_eq_24_log_x, h_log_w_eq_40_log_y]
  
  -- 24 * log x = 12 * (log x + log y + log z)
  have h_xyz_rel : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
    rw [h_log_prod] at h_log_w_eq_12_log_xyz
    linarith [h_log_w_eq_12_log_xyz]
  
  -- Simplify h_xyz_rel
  have h_simplify : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by
    linarith
  
  have h_log_x_eq : Real.log x = Real.log y + Real.log z := by linarith
  
  -- Substitute log x in h_xy_rel
  -- 24 * (log y + log z) = 40 * log y
  -- 24 log y + 24 log z = 40 log y
  -- 24 log z = 16 log y
  -- 3 log z = 2 log y => log z = (2/3) log y
  have h_log_z_in_terms_y : Real.log z = (2 : ℝ) / 3 * Real.log y := by
    have : 24 * (Real.log y + Real.log z) = 40 * Real.log y := by
      rw [h_log_x_eq] at h_xy_rel
      exact h_xy_rel
    field_simp at this ⊢
    linarith
  
  -- Final calculation
  -- log w / log z = (40 * log y) / log z
  -- = 40 * log y / ((2/3) * log y)
  -- = 40 / (2/3) = 60
  have h_final : Real.log w / Real.log z = 60 := by
    rw [h_log_w_eq_40_log_y, h_log_z_in_terms_y]
    field_simp [hz_log_ne_zero, hy_log_ne_zero]
    <;> ring_nf
    <;> norm_num
    <;> linarith
  
  exact h_final
