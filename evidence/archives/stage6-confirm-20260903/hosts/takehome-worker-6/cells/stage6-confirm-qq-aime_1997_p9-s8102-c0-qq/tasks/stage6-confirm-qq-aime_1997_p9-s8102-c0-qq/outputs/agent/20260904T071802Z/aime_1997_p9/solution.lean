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
    have h₅₂ : 1 / a < 1 := by
      have h₅₃ : a > 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      have h₅₄ : a^2 > 2 := h₂
      have h₅₅ : a > Real.sqrt 2 := by
        apply lt_of_sub_pos
        have h₅₆ : 0 < a := h₀
        have h₅₇ : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), h₅₄]
      have h₅₈ : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      exact h₅₈
    rw [Int.floor_eq_iff]
    norm_num at h₅₁ h₅₂ ⊢
    constructor <;> linarith
  
  -- Step 3: Simplify the main equation
  have h₆ : 1 / a = a^2 - 2 := by
    rw [h₅, h₄] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- Step 4: Derive the cubic equation
  have h₇ : a^3 - 2 * a - 1 = 0 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : 1 = a * (a^2 - 2) := by
      field_simp [h₀.ne'] at h₇₁
      linarith
    nlinarith
  
  -- Step 5: Factor the cubic equation to get quadratic
  have h₈ : a^2 - a - 1 = 0 := by
    have h₈₁ : (a + 1) * (a^2 - a - 1) = a^3 - 2 * a - 1 := by ring
    have h₈₂ : (a + 1) * (a^2 - a - 1) = 0 := by
      rw [h₈₁]
      linarith
    have h₈₃ : a + 1 ≠ 0 := by linarith
    have h₈₄ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₃
      linarith
    exact h₈₄
  
  -- Step 6: Express 1/a in terms of a
  have h₉ : 1 / a = a - 1 := by
    have h₉₁ : a^2 - a - 1 = 0 := h₈
    have h₉₂ : a ≠ 0 := by linarith
    have h₉₃ : a^2 = a + 1 := by linarith
    have h₉₄ : 1 = a * (a - 1) := by
      calc
        1 = a^2 - a := by linarith
        _ = a * a - a := by ring
        _ = a * (a - 1) := by ring
    field_simp [h₉₂] at h₉₄ ⊢
    linarith
  
  -- Step 7: Compute a^12 using a^2 = a + 1
  -- We know a^n = F_n * a + F_{n-1} where F_n are Fibonacci numbers
  -- F_12 = 144, F_11 = 89
  -- So a^12 = 144 * a + 89
  
  have h₁₀ : a^12 = 144 * a + 89 := by
    have h₁₀₁ : a^2 = a + 1 := by linarith
    have h₁₀₂ : a^3 = 2 * a + 1 := by
      calc
        a^3 = a * a^2 := by ring
        _ = a * (a + 1) := by rw [h₁₀₁]
        _ = a^2 + a := by ring
        _ = (a + 1) + a := by rw [h₁₀₁]
        _ = 2 * a + 1 := by ring
    have h₁₀₃ : a^4 = 3 * a + 2 := by
      calc
        a^4 = a * a^3 := by ring
        _ = a * (2 * a + 1) := by rw [h₁₀₂]
        _ = 2 * a^2 + a := by ring
        _ = 2 * (a + 1) + a := by rw [h₁₀₁]
        _ = 3 * a + 2 := by ring
    have h₁₀₄ : a^6 = 8 * a + 5 := by
      calc
        a^6 = (a^3)^2 := by ring
        _ = (2 * a + 1)^2 := by rw [h₁₀₂]
        _ = 4 * a^2 + 4 * a + 1 := by ring
        _ = 4 * (a + 1) + 4 * a + 1 := by rw [h₁₀₁]
        _ = 8 * a + 5 := by ring
    have h₁₀₅ : a^12 = (a^6)^2 := by ring
    have h₁₀₆ : a^12 = (8 * a + 5)^2 := by rw [h₁₀₅, h₁₀₄]
    have h₁₀₇ : a^12 = 64 * a^2 + 80 * a + 25 := by
      calc
        a^12 = (8 * a + 5)^2 := by rw [h₁₀₆]
        _ = 64 * a^2 + 80 * a + 25 := by ring
    have h₁₀₈ : a^12 = 64 * (a + 1) + 80 * a + 25 := by
      calc
        a^12 = 64 * a^2 + 80 * a + 25 := by rw [h₁₀₇]
        _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₁₀₁]
    have h₁₀₉ : a^12 = 144 * a + 89 := by
      calc
        a^12 = 64 * (a + 1) + 80 * a + 25 := by rw [h₁₀₈]
        _ = 64 * a + 64 + 80 * a + 25 := by ring
        _ = 144 * a + 89 := by ring
    exact h₁₀₉
  
  -- Step 8: Final calculation
  have h₁₁ : a^12 - 144 * (1 / a) = 233 := by
    calc
      a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
        rw [h₁₀, h₉]
      _ = 144 * a + 89 - 144 * a + 144 := by ring
      _ = 89 + 144 := by ring
      _ = 233 := by norm_num
  
  exact h₁₁
