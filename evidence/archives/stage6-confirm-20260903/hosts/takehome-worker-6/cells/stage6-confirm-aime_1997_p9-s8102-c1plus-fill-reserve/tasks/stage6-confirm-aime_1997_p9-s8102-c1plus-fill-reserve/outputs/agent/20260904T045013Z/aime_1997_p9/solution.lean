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
    constructor <;> linarith
  
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 0 < 1 / a := by positivity
    have h₅₂ : 1 / a < 1 := by
      have h₅₂₁ : a > 1 := by nlinarith [h₂, h₀]
      rw [div_lt_one (by positivity)]
      nlinarith
    rw [Int.floor_eq_iff]
    norm_num at h₅₁ h₅₂ ⊢
    constructor <;> linarith
  
  have h₆ : 1 / a = a^2 - 2 := by
    rw [h₅, h₄] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  have h₇ : a^3 - 2*a - 1 = 0 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : a ≠ 0 := by linarith
    field_simp [h₇₂] at h₇₁
    ring_nf at h₇₁ ⊢
    linarith
  
  have h₈ : a^3 = 2*a + 1 := by linarith
  
  have h₉ : a^6 = 4*a^2 + 4*a + 1 := by
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2*a + 1)^2 := by rw [h₈]
      _ = 4*a^2 + 4*a + 1 := by ring
  
  have h₁₀ : a^12 = 16*a^4 + 32*a^3 + 24*a^2 + 8*a + 1 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (4*a^2 + 4*a + 1)^2 := by rw [h₉]
      _ = 16*a^4 + 32*a^3 + 24*a^2 + 8*a + 1 := by ring
  
  have h₁₁ : a^4 = 2*a^2 + a := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2*a + 1) := by rw [h₈]
      _ = 2*a^2 + a := by ring
  
  have h₁₂ : a^12 = 56*a^2 + 88*a + 33 := by
    calc
      a^12 = 16*a^4 + 32*a^3 + 24*a^2 + 8*a + 1 := by rw [h₁₀]
      _ = 16*(2*a^2 + a) + 32*(2*a + 1) + 24*a^2 + 8*a + 1 := by
        rw [h₁₁, h₈]
        <;> ring
      _ = 56*a^2 + 88*a + 33 := by ring
  
  have h₁₃ : a^2 - a - 1 = 0 := by
    have h₁₃₁ : (a + 1) * (a^2 - a - 1) = 0 := by
      calc
        (a + 1) * (a^2 - a - 1) = a^3 - a^2 - a + a^2 - a - 1 := by ring
        _ = a^3 - 2*a - 1 := by ring
        _ = 0 := by rw [h₇]
    have h₁₃₂ : a + 1 ≠ 0 := by linarith
    have h₁₃₃ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₁₃₂
      linarith
    exact h₁₃₃
  
  have h₁₄ : a^12 - 144 * (1 / a) = 233 := by
    have h₁₄₁ : 1 / a = a^2 - 2 := h₆
    calc
      a^12 - 144 * (1 / a) = a^12 - 144 * (a^2 - 2) := by rw [h₁₄₁]
      _ = (56*a^2 + 88*a + 33) - 144*(a^2 - 2) := by rw [h₁₂]
      _ = 56*a^2 + 88*a + 33 - 144*a^2 + 288 := by ring
      _ = -88*a^2 + 88*a + 321 := by ring
      _ = 233 := by
        have h₁₄₂ : a^2 = a + 1 := by linarith [h₁₃]
        rw [h₁₄₂]
        ring
        <;> linarith
  
  exact h₁₄
