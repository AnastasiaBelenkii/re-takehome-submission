import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) : Real.log w / Real.log z = 60 := by
  -- Cast inequalities to reals
  have hx_gt_1 : (x : ℝ) > 1 := by exact_mod_cast ht.1
  have hy_gt_1 : (y : ℝ) > 1 := by exact_mod_cast ht.2.1
  have hz_gt_1 : (z : ℝ) > 1 := by exact_mod_cast ht.2.2
  
  -- Positivity of x, y, z
  have hx_pos : (x : ℝ) > 0 := by linarith [hx_gt_1]
  have hy_pos : (y : ℝ) > 0 := by linarith [hy_gt_1]
  have hz_pos : (z : ℝ) > 0 := by linarith [hz_gt_1]
  
  -- Non-zero logs for x, y, z
  have hx_log_ne_zero : Real.log x ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact hx_pos
    · exact hx_gt_1.ne'
  have hy_log_ne_zero : Real.log y ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact hy_pos
    · exact hy_gt_1.ne'
  have hz_log_ne_zero : Real.log z ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact hz_pos
    · exact hz_gt_1.ne'
  
  -- Derive log(w) relations
  have h3 : Real.log w = 24 * Real.log x := by
    field_simp [hx_log_ne_zero] at h0 ⊢
    linarith
  
  have h4 : Real.log w = 40 * Real.log y := by
    field_simp [hy_log_ne_zero] at h1 ⊢
    linarith
  
  -- Product log relation
  have hxyz_gt_1 : (x * y * z : ℝ) > 1 := by
    calc
      (x * y * z : ℝ) > 1 * 1 * 1 := by gcongr <;> assumption
      _ = 1 := by norm_num
  
  have hxyz_pos : (x * y * z : ℝ) > 0 := by linarith [hxyz_gt_1]
  
  have hxyz_log_ne_zero : Real.log (x * y * z) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact hxyz_pos
    · exact hxyz_gt_1.ne'
  
  have h5 : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) := by
    have h_log_prod : Real.log (x * y * z : ℝ) = Real.log x + Real.log y + Real.log z := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      <;> ring_nf
    field_simp [hxyz_log_ne_zero] at h2 ⊢
    rw [h_log_prod] at h2
    linarith
  
  -- Combine equations
  have h6 : 24 * Real.log x = 40 * Real.log y := by linarith
  have h7 : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by linarith
  
  -- Simplify h7
  have h8 : Real.log x = Real.log y + Real.log z := by
    linarith
  
  -- From h6: log(x) = (5/3) * log(y)
  have h9 : Real.log x = (5/3 : ℝ) * Real.log y := by
    field_simp [hy_log_ne_zero] at h6 ⊢
    linarith
  
  -- Substitute into h8
  have h10 : Real.log z = (2/3 : ℝ) * Real.log y := by
    rw [h9] at h8
    linarith
  
  -- Compute result
  have h11 : Real.log w / Real.log z = 60 := by
    field_simp [hz_log_ne_zero, hy_log_ne_zero]
    rw [h4, h10]
    ring_nf
    <;> norm_num
    <;> linarith
  
  exact h11
