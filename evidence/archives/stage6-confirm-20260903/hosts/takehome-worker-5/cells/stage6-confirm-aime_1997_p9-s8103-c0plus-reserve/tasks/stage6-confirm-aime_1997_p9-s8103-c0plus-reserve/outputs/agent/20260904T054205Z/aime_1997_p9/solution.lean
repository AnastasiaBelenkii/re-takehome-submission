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
    norm_num at h₂ h₃ ⊢
    constructor <;> linarith
  
  -- Determine floor(1/a)
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 1 / a < 1 := by
      have h₅₂ : a > 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      rw [div_lt_one (by positivity)]
      nlinarith
    have h₅₃ : 1 / a > 0 := by positivity
    rw [Int.floor_eq_iff]
    norm_num at h₅₁ h₅₃ ⊢
    constructor <;> linarith
  
  -- Simplify h₁ using floors
  have h₆ : 1 / a = a^2 - 2 := by
    rw [h₄, h₅] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- Derive polynomial equation for a
  have h₇ : a^3 - 2 * a - 1 = 0 := by
    have h₇₁ : a ≠ 0 := by linarith
    field_simp [h₇₁] at h₆
    ring_nf at h₆ ⊢
    linarith
  
  -- Factor the polynomial
  have h₈ : a^2 - a - 1 = 0 := by
    have h₈₁ : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf at h₇ ⊢
      linarith
    have h₈₂ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₈₂
    linarith
  
  -- Get relation a^2 = a + 1
  have h₉ : a^2 = a + 1 := by linarith
  
  -- Compute a^4
  have h₁₀ : a^4 = 3 * a + 2 := by
    calc
      a^4 = (a^2)^2 := by ring
      _ = (a + 1)^2 := by rw [h₉]
      _ = a^2 + 2 * a + 1 := by ring
      _ = (a + 1) + 2 * a + 1 := by rw [h₉]
      _ = 3 * a + 2 := by ring
  
  -- Compute a^8
  have h₁₁ : a^8 = 21 * a + 13 := by
    calc
      a^8 = (a^4)^2 := by ring
      _ = (3 * a + 2)^2 := by rw [h₁₀]
      _ = 9 * a^2 + 12 * a + 4 := by ring
      _ = 9 * (a + 1) + 12 * a + 4 := by rw [h₉]
      _ = 21 * a + 13 := by ring
  
  -- Compute a^12
  have h₁₂ : a^12 = 144 * a + 89 := by
    calc
      a^12 = a^8 * a^4 := by ring
      _ = (21 * a + 13) * (3 * a + 2) := by rw [h₁₁, h₁₀]
      _ = 63 * a^2 + 42 * a + 39 * a + 26 := by ring
      _ = 63 * (a + 1) + 81 * a + 26 := by rw [h₉]; ring
      _ = 144 * a + 89 := by ring
  
  -- Compute 1/a
  have h₁₃ : 1 / a = a - 1 := by
    have h₁₃₁ : a ≠ 0 := by linarith
    have h₁₃₂ : a^2 = a + 1 := h₉
    field_simp [h₁₃₁]
    nlinarith
  
  -- Final calculation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (1 / a) := by rw [h₁₂]
    _ = (144 * a + 89) - 144 * (a - 1) := by rw [h₁₃]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
