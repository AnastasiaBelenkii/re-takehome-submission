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
  -- From h₂ and h₃, we have 2 < a² < 3, so floor(a²) = 2
  have h₄ : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num at h₂ h₃ ⊢
    constructor <;> norm_cast <;> linarith
  
  -- Since 2 < a² < 3, we have √2 < a < √3, so 1 < a < 2
  -- Therefore 1/2 < 1/a < 1, so floor(1/a) = 0
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : a > 1 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    have h₅₂ : a < 2 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    have h₅₃ : 1 / a < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    have h₅₄ : 1 / a > 0 := by positivity
    rw [Int.floor_eq_iff]
    norm_num at h₅₃ h₅₄ ⊢
    constructor <;> norm_cast <;> linarith
  
  -- Substitute floor values into h₁ to get 1/a = a² - 2
  have h₆ : 1 / a = a^2 - 2 := by
    rw [h₅, h₄] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- From h₆, we get a³ = 2a + 1
  have h₇ : a^3 = 2 * a + 1 := by
    have h₇₁ : a ≠ 0 := by linarith
    field_simp [h₇₁] at h₆
    nlinarith
  
  -- Prove a^2 - a - 1 = 0
  have h₈ : a^2 - a - 1 = 0 := by
    have h₈₁ : (a + 1) * (a^2 - a - 1) = a^3 - 2 * a - 1 := by ring
    have h₈₂ : a^3 - 2 * a - 1 = 0 := by
      rw [h₇]
      ring
    have h₈₃ : a + 1 ≠ 0 := by linarith
    have h₈₄ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₃
      linarith
    exact h₈₄
  
  -- From h₈, we have a^2 = a + 1 and 1/a = a - 1
  have h₉ : a^2 = a + 1 := by linarith
  have h₁₀ : 1 / a = a - 1 := by
    have h₁₀₁ : a ≠ 0 := by linarith
    have h₁₀₂ : a * (a - 1) = 1 := by
      calc
        a * (a - 1) = a^2 - a := by ring
        _ = 1 := by linarith
    field_simp [h₁₀₁]
    linarith
  
  -- Calculate a^12 using a^2 = a + 1
  have h₁₁ : a^6 = 8 * a + 5 := by
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2 * a + 1)^2 := by rw [h₇]
      _ = 4 * a^2 + 4 * a + 1 := by ring
      _ = 4 * (a + 1) + 4 * a + 1 := by rw [h₉]
      _ = 8 * a + 5 := by ring
  
  have h₁₂ : a^12 = 144 * a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8 * a + 5)^2 := by rw [h₁₁]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₉]
      _ = 144 * a + 89 := by ring
  
  -- Final calculation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₁₂, h₁₀]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
