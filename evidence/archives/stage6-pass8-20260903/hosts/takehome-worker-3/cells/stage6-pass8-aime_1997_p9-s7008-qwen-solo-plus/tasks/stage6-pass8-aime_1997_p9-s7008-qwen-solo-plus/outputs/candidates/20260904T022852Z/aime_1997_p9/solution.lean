import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1997_p9
  (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2))
  (h₂ : 2 < a^2)
  (h₃ : a^2 < 3) :
  a^12 - 144 * (1 / a) = 233 := by
  have h_floor_a2 : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num at h₂ h₃ ⊢
    constructor <;> norm_num <;> linarith
  
  have h_a_gt_sqrt2 : a > Real.sqrt 2 := by
    have h_sqrt_sq : (Real.sqrt 2)^2 = 2 := by norm_num [Real.sq_sqrt]
    have h_pos : 0 ≤ a := by linarith
    have h_pos_sqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    -- Use the fact that if a^2 > 2 and a > 0, then a > sqrt(2)
    have h_main : a > Real.sqrt 2 := by
      by_contra h
      have h' : a ≤ Real.sqrt 2 := by linarith
      have h'' : a^2 ≤ (Real.sqrt 2)^2 := by
        gcongr
      rw [h_sqrt_sq] at h''
      linarith
    exact h_main
  
  have h_inv_lt_one : 1 / a < 1 := by
    have h_a_gt_sqrt2 : a > Real.sqrt 2 := h_a_gt_sqrt2
    have h_sqrt2_gt_1 : Real.sqrt 2 > 1 := by norm_num [Real.lt_sqrt]
    have h_a_gt_1 : a > 1 := by linarith
    have h_inv_lt_one : 1 / a < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    exact h_inv_lt_one
  
  have h_floor_inv_a : Int.floor (1 / a) = 0 := by
    have h_pos : 0 < 1 / a := by positivity
    rw [Int.floor_eq_iff]
    norm_num at h_pos h_inv_lt_one ⊢
    constructor <;> norm_num <;> linarith

  have h_main_eq : 1 / a = a^2 - 2 := by
    have h₁' : 1 / a - ↑(Int.floor (1 / a)) = a^2 - ↑(Int.floor (a^2)) := by simpa using h₁
    rw [h_floor_a2, h_floor_inv_a] at h₁'
    ring_nf at h₁' ⊢
    linarith

  have h_poly : a^3 - 2 * a - 1 = 0 := by
    have h_a_ne_zero : a ≠ 0 := by linarith
    field_simp [h_a_ne_zero] at h_main_eq ⊢
    nlinarith

  have h_quad : a^2 - a - 1 = 0 := by
    have h_factor : (a + 1) * (a^2 - a - 1) = a^3 - 2 * a - 1 := by ring
    rw [h_poly] at h_factor
    have h_sum_pos : a + 1 > 0 := by linarith
    have h_sum_ne_zero : a + 1 ≠ 0 := by linarith
    have h_prod_zero : (a + 1) * (a^2 - a - 1) = 0 := by linarith
    apply mul_left_cancel₀ h_sum_ne_zero
    linarith

  have h_a2 : a^2 = a + 1 := by linarith
  have h_a3 : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [h_a2]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h_a2]
      _ = 2 * a + 1 := by ring
  
  have h_a6 : a^6 = 8 * a + 5 := by
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2 * a + 1)^2 := by rw [h_a3]
      _ = 4 * a^2 + 4 * a + 1 := by ring
      _ = 4 * (a + 1) + 4 * a + 1 := by rw [h_a2]
      _ = 8 * a + 5 := by ring
  
  have h_a12 : a^12 = 144 * a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8 * a + 5)^2 := by rw [h_a6]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h_a2]
      _ = 144 * a + 89 := by ring

  have h_inv_a : 1 / a = a - 1 := by
    calc
      1 / a = a^2 - 2 := by rw [h_main_eq]
      _ = (a + 1) - 2 := by rw [h_a2]
      _ = a - 1 := by ring

  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by rw [h_a12, h_inv_a]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
