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
      have h₅₃ : 1 < a := by
        by_contra h
        have : a ≤ 1 := by linarith
        have : a^2 ≤ 1 := by nlinarith
        linarith
      rw [div_lt_one (by positivity)]
      nlinarith
    rw [Int.floor_eq_iff]
    norm_num at h₅₁ h₅₂ ⊢
    constructor <;> linarith
  
  have h₆ : 1 / a = a^2 - 2 := by
    have h₆₁ : (1 / a : ℝ) - ↑(Int.floor (1 / a)) = a^2 - ↑(Int.floor (a^2)) := by simpa using h₁
    rw [h₅, h₄] at h₆₁
    ring_nf at h₆₁ ⊢
    linarith
  
  have h₇ : a^3 - 2 * a - 1 = 0 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : a ≠ 0 := by linarith
    field_simp [h₇₂] at h₇₁
    ring_nf at h₇₁ ⊢
    linarith
  
  have h₈ : a^2 - a - 1 = 0 := by
    have h₈₁ : (a + 1) * (a^2 - a - 1) = a^3 - 2 * a - 1 := by ring
    have h₈₂ : (a + 1) * (a^2 - a - 1) = 0 := by
      rw [h₈₁]
      rw [h₇]
    have h₈₃ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₈₃
    linarith
  
  have h₉ : a^2 = a + 1 := by linarith
  
  have h₁₀ : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [h₉]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h₉]
      _ = 2 * a + 1 := by ring
  
  have h₁₁ : a^4 = 3 * a + 2 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2 * a + 1) := by rw [h₁₀]
      _ = 2 * a^2 + a := by ring
      _ = 2 * (a + 1) + a := by rw [h₉]
      _ = 3 * a + 2 := by ring
  
  have h₁₂ : a^5 = 5 * a + 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (3 * a + 2) := by rw [h₁₁]
      _ = 3 * a^2 + 2 * a := by ring
      _ = 3 * (a + 1) + 2 * a := by rw [h₉]
      _ = 5 * a + 3 := by ring
  
  have h₁₃ : a^6 = 8 * a + 5 := by
    calc
      a^6 = a * a^5 := by ring
      _ = a * (5 * a + 3) := by rw [h₁₂]
      _ = 5 * a^2 + 3 * a := by ring
      _ = 5 * (a + 1) + 3 * a := by rw [h₉]
      _ = 8 * a + 5 := by ring
  
  have h₁₄ : a^12 = 144 * a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8 * a + 5)^2 := by rw [h₁₃]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₉]
      _ = 144 * a + 89 := by ring
  
  have h₁₅ : 1 / a = a - 1 := by
    have h₁₅₁ : 1 / a = a^2 - 2 := h₆
    rw [h₁₅₁]
    rw [h₉]
    ring
  
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₁₄, h₁₅]
      <;> ring
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
