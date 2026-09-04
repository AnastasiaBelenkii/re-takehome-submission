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
  have h₄ : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num at h₂ h₃ ⊢
    constructor <;> norm_cast <;> linarith
  
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 0 < a := h₀
    have h₅₂ : 2 < a^2 := h₂
    have h₅₃ : a^2 < 3 := h₃
    have h₅₄ : 0 < a^2 := by positivity
    have h₅₅ : 1 / a > 0 := by positivity
    have h₅₆ : 1 / a < 1 := by
      have h₅₆₁ : a^2 > 2 := h₂
      have h₅₆₂ : a > Real.sqrt 2 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      have h₅₆₃ : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact h₅₆₃
    rw [Int.floor_eq_iff]
    norm_num at h₅₅ h₅₆ ⊢
    constructor <;> norm_num <;> linarith
  
  have h₆ : 1 / a = a^2 - 2 := by
    have h₆₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2) := h₁
    rw [h₅, h₄] at h₆₁
    ring_nf at h₆₁ ⊢
    linarith
  
  have h₇ : a^3 - 2 * a - 1 = 0 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : 1 = a * (a^2 - 2) := by
      field_simp [h₀.ne'] at h₇₁ ⊢
      linarith
    nlinarith
  
  have h₈ : a^2 = a + 1 := by
    have h₈₁ : a^3 - 2 * a - 1 = 0 := h₇
    have h₈₂ : (a + 1) * (a^2 - a - 1) = 0 := by
      nlinarith
    have h₈₃ : a + 1 ≠ 0 := by
      nlinarith [h₀]
    have h₈₄ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₃
      nlinarith
    nlinarith
  
  have h₉ : a^12 = 144 * a + 89 := by
    have h₉₁ : a^2 = a + 1 := h₈
    have h₉₂ : a^3 = 2 * a + 1 := by
      calc
        a^3 = a * a^2 := by ring
        _ = a * (a + 1) := by rw [h₉₁]
        _ = a^2 + a := by ring
        _ = (a + 1) + a := by rw [h₉₁]
        _ = 2 * a + 1 := by ring
    have h₉₃ : a^4 = 3 * a + 2 := by
      calc
        a^4 = a * a^3 := by ring
        _ = a * (2 * a + 1) := by rw [h₉₂]
        _ = 2 * a^2 + a := by ring
        _ = 2 * (a + 1) + a := by rw [h₉₁]
        _ = 3 * a + 2 := by ring
    have h₉₄ : a^5 = 5 * a + 3 := by
      calc
        a^5 = a * a^4 := by ring
        _ = a * (3 * a + 2) := by rw [h₉₃]
        _ = 3 * a^2 + 2 * a := by ring
        _ = 3 * (a + 1) + 2 * a := by rw [h₉₁]
        _ = 5 * a + 3 := by ring
    have h₉₅ : a^6 = 8 * a + 5 := by
      calc
        a^6 = a * a^5 := by ring
        _ = a * (5 * a + 3) := by rw [h₉₄]
        _ = 5 * a^2 + 3 * a := by ring
        _ = 5 * (a + 1) + 3 * a := by rw [h₉₁]
        _ = 8 * a + 5 := by ring
    have h₉₆ : a^7 = 13 * a + 8 := by
      calc
        a^7 = a * a^6 := by ring
        _ = a * (8 * a + 5) := by rw [h₉₅]
        _ = 8 * a^2 + 5 * a := by ring
        _ = 8 * (a + 1) + 5 * a := by rw [h₉₁]
        _ = 13 * a + 8 := by ring
    have h₉₇ : a^8 = 21 * a + 13 := by
      calc
        a^8 = a * a^7 := by ring
        _ = a * (13 * a + 8) := by rw [h₉₆]
        _ = 13 * a^2 + 8 * a := by ring
        _ = 13 * (a + 1) + 8 * a := by rw [h₉₁]
        _ = 21 * a + 13 := by ring
    have h₉₈ : a^9 = 34 * a + 21 := by
      calc
        a^9 = a * a^8 := by ring
        _ = a * (21 * a + 13) := by rw [h₉₇]
        _ = 21 * a^2 + 13 * a := by ring
        _ = 21 * (a + 1) + 13 * a := by rw [h₉₁]
        _ = 34 * a + 21 := by ring
    have h₉₉ : a^10 = 55 * a + 34 := by
      calc
        a^10 = a * a^9 := by ring
        _ = a * (34 * a + 21) := by rw [h₉₈]
        _ = 34 * a^2 + 21 * a := by ring
        _ = 34 * (a + 1) + 21 * a := by rw [h₉₁]
        _ = 55 * a + 34 := by ring
    have h₉₁₀ : a^11 = 89 * a + 55 := by
      calc
        a^11 = a * a^10 := by ring
        _ = a * (55 * a + 34) := by rw [h₉₉]
        _ = 55 * a^2 + 34 * a := by ring
        _ = 55 * (a + 1) + 34 * a := by rw [h₉₁]
        _ = 89 * a + 55 := by ring
    calc
      a^12 = a * a^11 := by ring
      _ = a * (89 * a + 55) := by rw [h₉₁₀]
      _ = 89 * a^2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [h₉₁]
      _ = 144 * a + 89 := by ring
  
  have h₁₀ : 1 / a = a - 1 := by
    have h₁₀₁ : a^2 = a + 1 := h₈
    have h₁₀₂ : a ≠ 0 := by linarith
    have h₁₀₃ : 1 / a = a - 1 := by
      have h₁₀₄ : a * (a - 1) = 1 := by
        nlinarith [h₈]
      field_simp [h₁₀₂] at h₁₀₄ ⊢
      nlinarith
    exact h₁₀₃
  
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₉, h₁₀]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
