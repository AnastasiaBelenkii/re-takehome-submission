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
  -- Step 1: Determine floor values from bounds
  have h_floor_a2 : Int.floor (a^2) = 2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h₂ h₃ ⊢ <;> linarith
  
  have h_floor_1a : Int.floor (1 / a) = 0 := by
    have h_a_gt_1 : 1 < a := by
      nlinarith [h₂, h₀]
    have h_1a_pos : 0 < 1 / a := by positivity
    have h_1a_lt_1 : 1 / a < 1 := by
      rw [div_lt_one (by positivity)]
      exact h_a_gt_1
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h_1a_pos h_1a_lt_1 ⊢ <;> linarith
  
  -- Step 2: Use the fractional part equality to derive the key equation
  have h_key_eq : 1 / a = a^2 - 2 := by
    have h_frac_eq : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2) := h₁
    rw [h_floor_1a, h_floor_a2] at h_frac_eq
    ring_nf at h_frac_eq ⊢
    linarith
  
  -- Step 3: Derive polynomial equation for a
  have h_poly : a^3 - 2*a - 1 = 0 := by
    have h_inv_a : 1 / a = a^2 - 2 := h_key_eq
    have h_a_ne_zero : a ≠ 0 := by linarith
    field_simp [h_a_ne_zero] at h_inv_a
    nlinarith
  
  -- Step 4: Show a^2 = a + 1 (golden ratio property)
  have h_golden : a^2 = a + 1 := by
    have h_poly_factored : (a + 1) * (a^2 - a - 1) = 0 := by
      nlinarith [h_poly]
    have h_a_plus_1_ne_zero : a + 1 ≠ 0 := by linarith
    have h_quad_eq : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h_a_plus_1_ne_zero
      nlinarith
    nlinarith
  
  -- Step 5: Compute a^12 using Fibonacci recurrence
  have h_a12 : a^12 = 144 * a + 89 := by
    have h_a2 : a^2 = a + 1 := h_golden
    have h_a3 : a^3 = 2 * a + 1 := by nlinarith
    have h_a4 : a^4 = 3 * a + 2 := by nlinarith
    have h_a5 : a^5 = 5 * a + 3 := by nlinarith
    have h_a6 : a^6 = 8 * a + 5 := by nlinarith
    have h_a7 : a^7 = 13 * a + 8 := by nlinarith
    have h_a8 : a^8 = 21 * a + 13 := by nlinarith
    have h_a9 : a^9 = 34 * a + 21 := by nlinarith
    have h_a10 : a^10 = 55 * a + 34 := by nlinarith
    have h_a11 : a^11 = 89 * a + 55 := by nlinarith
    nlinarith
  
  -- Step 6: Final computation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a^2 - 2) := by
      rw [h_a12, h_key_eq]
    _ = 144 * a + 89 - 144 * a^2 + 288 := by ring
    _ = 144 * a + 89 - 144 * (a + 1) + 288 := by rw [h_golden]
    _ = 144 * a + 89 - 144 * a - 144 + 288 := by ring
    _ = 233 := by ring
