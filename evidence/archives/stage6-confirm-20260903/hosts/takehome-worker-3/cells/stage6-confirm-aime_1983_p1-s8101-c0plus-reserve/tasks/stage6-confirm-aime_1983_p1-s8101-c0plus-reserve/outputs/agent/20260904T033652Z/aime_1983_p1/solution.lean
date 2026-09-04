import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast naturals to reals for easier manipulation
  have hxR : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hyR : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hzR : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  
  -- Establish positivity and non-one conditions for logs
  have hx_pos : (x : ℝ) > 0 := by linarith
  have hy_pos : (y : ℝ) > 0 := by linarith
  have hz_pos : (z : ℝ) > 0 := by linarith
  
  have hx_ne_one : (x : ℝ) ≠ 1 := by
    intro h
    linarith [hxR]
  have hy_ne_one : (y : ℝ) ≠ 1 := by
    intro h
    linarith [hyR]
  have hz_ne_one : (z : ℝ) ≠ 1 := by
    intro h
    linarith [hzR]
  
  -- Logarithm properties
  have hx_log_ne_zero : Real.log (x : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx_pos hx_ne_one
  have hy_log_ne_zero : Real.log (y : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy_pos hy_ne_one
  have hz_log_ne_zero : Real.log (z : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hz_pos hz_ne_one
  
  -- Expand log(x*y*z)
  have h_log_prod : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) = Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    <;> simp [mul_assoc]
  
  -- Extract relations from hypotheses
  -- h0: log w = 24 * log x
  have h_w_eq_24_log_x : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := by
    have h_denom_ne_zero : Real.log (x : ℝ) ≠ 0 := hx_log_ne_zero
    field_simp [h_denom_ne_zero] at h0 ⊢
    linarith
  
  -- h1: log w = 40 * log y
  have h_w_eq_40_log_y : Real.log (w : ℝ) = 40 * Real.log (y : ℝ) := by
    have h_denom_ne_zero : Real.log (y : ℝ) ≠ 0 := hy_log_ne_zero
    field_simp [h_denom_ne_zero] at h1 ⊢
    linarith
  
  -- h2: log w = 12 * log(xyz)
  have h_w_eq_12_log_xyz : Real.log (w : ℝ) = 12 * Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) := by
    have h_denom_ne_zero : Real.log ((x : ℝ) * (y : ℝ) * (z : ℝ)) ≠ 0 := by
      have h_prod_ne_one : (x : ℝ) * (y : ℝ) * (z : ℝ) ≠ 1 := by
        have h_prod_gt_one : (x : ℝ) * (y : ℝ) * (z : ℝ) > 1 := by
          calc
            (x : ℝ) * (y : ℝ) * (z : ℝ) > 1 * 1 * 1 := by gcongr <;> assumption
            _ = 1 := by norm_num
        linarith
      exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) h_prod_ne_one
    field_simp [h_denom_ne_zero] at h2 ⊢
    linarith
  
  -- Combine equations
  -- 24 * log x = 40 * log y => 3 * log x = 5 * log y
  have h_xy_rel : 3 * Real.log (x : ℝ) = 5 * Real.log (y : ℝ) := by
    have h_eq : 24 * Real.log (x : ℝ) = 40 * Real.log (y : ℝ) := by
      rw [← h_w_eq_24_log_x, ← h_w_eq_40_log_y]
    linarith
  
  -- 24 * log x = 12 * (log x + log y + log z) => 2 * log x = log x + log y + log z => log x = log y + log z
  have h_x_y_z_rel : Real.log (x : ℝ) = Real.log (y : ℝ) + Real.log (z : ℝ) := by
    have h_eq : 24 * Real.log (x : ℝ) = 12 * (Real.log (x : ℝ) + Real.log (y : ℝ) + Real.log (z : ℝ)) := by
      rw [← h_w_eq_24_log_x, h_w_eq_12_log_xyz, h_log_prod]
    linarith
  
  -- Solve for log z
  -- From h_x_y_z_rel: log y = log x - log z
  -- Substitute into h_xy_rel: 3 * log x = 5 * (log x - log z)
  -- 3 * log x = 5 * log x - 5 * log z
  -- 5 * log z = 2 * log x
  have h_z_in_terms_of_x : Real.log (z : ℝ) = (2 / 5 : ℝ) * Real.log (x : ℝ) := by
    have h_sub : Real.log (y : ℝ) = Real.log (x : ℝ) - Real.log (z : ℝ) := by linarith
    rw [h_sub] at h_xy_rel
    ring_nf at h_xy_rel ⊢
    linarith
  
  -- Calculate target
  -- log w / log z = (24 * log x) / ((2/5) * log x) = 24 / (2/5) = 60
  have h_final : Real.log (w : ℝ) / Real.log (z : ℝ) = 60 := by
    have h_denom_ne_zero : Real.log (z : ℝ) ≠ 0 := hz_log_ne_zero
    have h_w_val : Real.log (w : ℝ) = 24 * Real.log (x : ℝ) := h_w_eq_24_log_x
    rw [h_w_val, h_z_in_terms_of_x]
    field_simp [h_denom_ne_zero, hx_log_ne_zero]
    <;> ring_nf
    <;> norm_num
  
  exact h_final
