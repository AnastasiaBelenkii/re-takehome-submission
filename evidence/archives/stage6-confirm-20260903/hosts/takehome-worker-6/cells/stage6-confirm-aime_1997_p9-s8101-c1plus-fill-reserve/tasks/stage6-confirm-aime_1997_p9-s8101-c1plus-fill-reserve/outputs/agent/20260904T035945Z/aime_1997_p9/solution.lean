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
  -- Determine floor(a^2)
  have h₄ : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try linarith) <;>
      (try exact_mod_cast h₂) <;>
      (try exact_mod_cast h₃)
  
  -- Determine floor(1/a)
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 0 < a := h₀
    have h₅₂ : a^2 < 3 := h₃
    have h₅₃ : a < Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    have h₅₄ : 1 / a > 0 := by positivity
    have h₅₅ : 1 / a < 1 := by
      have h₅₅₁ : a > 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      rw [div_lt_one (by positivity)]
      nlinarith
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₅₄ h₅₅ ⊢ <;>
      (try linarith) <;>
      (try exact_mod_cast h₅₄) <;>
      (try exact_mod_cast h₅₅)
  
  -- Simplify h₁ using h₄ and h₅
  have h₆ : 1 / a = a^2 - 2 := by
    have h₆₁ : 1 / a - (Int.floor (1 / a) : ℝ) = a^2 - (Int.floor (a^2) : ℝ) := by
      simpa using h₁
    rw [h₄, h₅] at h₆₁
    norm_num at h₆₁ ⊢
    linarith
  
  -- Derive cubic equation
  have h₇ : a^3 - 2*a - 1 = 0 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : a ≠ 0 := by linarith
    field_simp [h₇₂] at h₇₁
    ring_nf at h₇₁
    linarith
  
  -- Factor cubic to find quadratic relation
  have h₈ : a^2 = a + 1 := by
    have h₈₁ : a^3 - 2*a - 1 = 0 := h₇
    have h₈₂ : a > 0 := h₀
    have h₈₃ : a^3 - 2*a - 1 = (a + 1) * (a^2 - a - 1) := by ring
    rw [h₈₃] at h₈₁
    have h₈₄ : (a + 1) * (a^2 - a - 1) = 0 := by linarith
    have h₈₅ : a + 1 ≠ 0 := by linarith
    have h₈₆ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₅
      linarith
    linarith
  
  -- Calculate powers of a
  have h₉₁ : a^3 = 2*a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [h₈]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h₈]
      _ = 2*a + 1 := by ring
  
  have h₉₂ : a^4 = 3*a + 2 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2*a + 1) := by rw [h₉₁]
      _ = 2*a^2 + a := by ring
      _ = 2*(a + 1) + a := by rw [h₈]
      _ = 3*a + 2 := by ring
  
  have h₉₃ : a^5 = 5*a + 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (3*a + 2) := by rw [h₉₂]
      _ = 3*a^2 + 2*a := by ring
      _ = 3*(a + 1) + 2*a := by rw [h₈]
      _ = 5*a + 3 := by ring
  
  have h₉₄ : a^6 = 8*a + 5 := by
    calc
      a^6 = a * a^5 := by ring
      _ = a * (5*a + 3) := by rw [h₉₃]
      _ = 5*a^2 + 3*a := by ring
      _ = 5*(a + 1) + 3*a := by rw [h₈]
      _ = 8*a + 5 := by ring
  
  have h₉₅ : a^12 = 144*a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8*a + 5)^2 := by rw [h₉₄]
      _ = 64*a^2 + 80*a + 25 := by ring
      _ = 64*(a + 1) + 80*a + 25 := by rw [h₈]
      _ = 144*a + 89 := by ring
  
  -- Calculate 1/a
  have h₁₀ : 1 / a = a - 1 := by
    have h₁₀₁ : 1 / a = a^2 - 2 := h₆
    have h₁₀₂ : a^2 = a + 1 := h₈
    calc
      1 / a = a^2 - 2 := by rw [h₁₀₁]
      _ = (a + 1) - 2 := by rw [h₁₀₂]
      _ = a - 1 := by ring
  
  -- Final calculation
  calc
    a^12 - 144 * (1 / a) = (144*a + 89) - 144 * (a - 1) := by
      rw [h₉₅, h₁₀]
    _ = 144*a + 89 - 144*a + 144 := by ring
    _ = 233 := by ring
