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
  -- From h₂ and h₃, we know 2 < a² < 3, so floor(a²) = 2
  have h_floor_a2 : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try norm_cast) <;>
      (try linarith) <;>
      (try nlinarith)
  
  -- Substitute floor(a²) = 2 into h₁
  have h_frac_eq : 1 / a - Int.floor (1 / a) = a^2 - 2 := by
    rw [h_floor_a2] at h₁
    exact h₁
  
  -- Since 2 < a² < 3, we have sqrt(2) < a < sqrt(3), so 1/sqrt(3) < 1/a < 1/sqrt(2)
  -- This means 0 < 1/a < 1, so floor(1/a) = 0
  have h_floor_1a : Int.floor (1 / a) = 0 := by
    have h_1a_pos : 0 < 1 / a := by positivity
    have h_1a_lt_one : 1 / a < 1 := by
      have h_a_gt_sqrt2 : Real.sqrt 2 < a := by
        apply lt_of_not_ge
        intro h
        have : a^2 ≤ 2 := by
          have : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg _
          nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
        linarith
      have : a^2 > 2 := h₂
      have : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact this
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h_1a_pos h_1a_lt_one ⊢ <;>
      (try norm_cast) <;>
      (try linarith)
  
  -- Now we have 1/a = a² - 2
  have h_main_eq : 1 / a = a^2 - 2 := by
    rw [h_floor_1a] at h_frac_eq
    linarith
  
  -- This gives us a³ - 2a - 1 = 0
  have h_cubic : a^3 - 2*a - 1 = 0 := by
    have h_inv : 1 = a * (a^2 - 2) := by
      field_simp [h₀.ne'] at h_main_eq ⊢
      nlinarith
    nlinarith
  
  -- We need to compute a^12 - 144/a
  -- First, let's find a relation for higher powers
  have h_a_sq : a^2 = a + 1 := by
    have h_factored : (a + 1) * (a^2 - a - 1) = 0 := by
      nlinarith [h_cubic]
    have h_a_plus_1_ne_zero : a + 1 ≠ 0 := by
      nlinarith [h₀]
    have h_a_sq_minus_a_minus_1 : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h_a_plus_1_ne_zero
      nlinarith
    nlinarith
  
  -- Use the recurrence to compute higher powers
  have h_a_3 : a^3 = 2*a + 1 := by
    nlinarith [h_a_sq]
  
  have h_a_4 : a^4 = 3*a + 2 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2*a + 1) := by rw [h_a_3]
      _ = 2*a^2 + a := by ring
      _ = 2*(a + 1) + a := by rw [h_a_sq]
      _ = 3*a + 2 := by ring
  
  have h_a_6 : a^6 = 8*a + 5 := by
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2*a + 1)^2 := by rw [h_a_3]
      _ = 4*a^2 + 4*a + 1 := by ring
      _ = 4*(a + 1) + 4*a + 1 := by rw [h_a_sq]
      _ = 8*a + 5 := by ring
  
  have h_a_12 : a^12 = 144*a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8*a + 5)^2 := by rw [h_a_6]
      _ = 64*a^2 + 80*a + 25 := by ring
      _ = 64*(a + 1) + 80*a + 25 := by rw [h_a_sq]
      _ = 144*a + 89 := by ring
  
  -- Now compute a^12 - 144/a
  have h_final : a^12 - 144 * (1 / a) = 233 := by
    have h_inv_a : 1 / a = a^2 - 2 := h_main_eq
    calc
      a^12 - 144 * (1 / a) = a^12 - 144 * (a^2 - 2) := by rw [h_inv_a]
      _ = (144*a + 89) - 144 * (a^2 - 2) := by rw [h_a_12]
      _ = 144*a + 89 - 144*a^2 + 288 := by ring
      _ = 144*a + 377 - 144*a^2 := by ring
      _ = 144*a + 377 - 144*(a + 1) := by rw [h_a_sq]
      _ = 144*a + 377 - 144*a - 144 := by ring
      _ = 233 := by ring
  
  exact h_final
