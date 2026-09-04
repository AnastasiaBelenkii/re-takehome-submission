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
  -- Step 1: Determine floor(a^2)
  have h₄ : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num at h₂ h₃ ⊢
    constructor <;> linarith
  
  -- Step 2: Determine floor(1/a)
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 0 < 1 / a := by positivity
    have h₅₃ : 1 < a := by
      nlinarith
    have h₅₂ : 1 / a < 1 := by
      rw [← sub_pos]
      field_simp [h₀.ne']
      nlinarith
    rw [Int.floor_eq_iff]
    norm_num at h₅₁ h₅₂ ⊢
    constructor <;> linarith
  
  -- Step 3: Simplify the main equation
  have h₆ : 1 / a = a^2 - 2 := by
    have h₆₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2) := h₁
    rw [h₅, h₄] at h₆₁
    ring_nf at h₆₁ ⊢
    linarith
  
  -- Step 4: Derive polynomial relation a^3 = 2a + 1
  have h₇ : a^3 = 2 * a + 1 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : a ≠ 0 := by linarith
    field_simp [h₇₂] at h₇₁
    ring_nf at h₇₁ ⊢
    linarith
  
  -- Step 5: Derive quadratic relation a^2 = a + 1
  have h₈ : a^2 = a + 1 := by
    have h₈₁ : a^3 - 2 * a - 1 = 0 := by
      have h₈₂ : a^3 = 2 * a + 1 := h₇
      linarith
    have h₈₃ : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf
      linarith
    have h₈₄ : a + 1 ≠ 0 := by linarith
    have h₈₅ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₄
      linarith
    linarith
  
  -- Step 6: Calculate a^6
  have h₉ : a^6 = 8 * a + 5 := by
    have h₉₁ : a^3 = 2 * a + 1 := h₇
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2 * a + 1)^2 := by rw [h₉₁]
      _ = 4 * a^2 + 4 * a + 1 := by ring
      _ = 4 * (a + 1) + 4 * a + 1 := by rw [h₈]
      _ = 8 * a + 5 := by ring
  
  -- Step 7: Calculate a^12
  have h₁₀ : a^12 = 144 * a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8 * a + 5)^2 := by rw [h₉]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₈]
      _ = 144 * a + 89 := by ring
  
  -- Step 8: Calculate 1/a
  have h₁₁ : 1 / a = a - 1 := by
    have h₁₁₁ : a^2 = a + 1 := h₈
    have h₁₁₂ : a ≠ 0 := by linarith
    have h₁₁₃ : a = 1 + 1 / a := by
      field_simp [h₁₁₂] at h₁₁₁ ⊢
      nlinarith
    linarith
  
  -- Step 9: Final computation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₁₀, h₁₁]
    _ = 233 := by ring
