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
    have h₄₁ : (2 : ℝ) ≤ a^2 := by linarith
    have h₄₂ : a^2 < (3 : ℝ) := by exact_mod_cast h₃
    rw [Int.floor_eq_iff]
    norm_num at h₄₁ h₄₂ ⊢
    constructor <;> norm_num <;> linarith
  
  -- Step 2: Simplify h₁ using h₄
  have h₅ : 1 / a - Int.floor (1 / a) = a^2 - 2 := by
    rw [h₄] at h₁
    exact h₁
  
  -- Step 3: Determine floor(1/a)
  have h₆ : Int.floor (1 / a) = 0 := by
    have h₆₁ : a^2 > 2 := by exact_mod_cast h₂
    have h₆₂ : a^2 < 3 := by exact_mod_cast h₃
    have h₆₃ : 0 < a := h₀
    have h₆₄ : a > Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    have h₆₅ : a < Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
    
    -- Show 1/a < 1/sqrt(2)
    have h₆₆ : 1 / a < 1 / Real.sqrt 2 := by
      apply one_div_lt_one_div_of_lt
      · norm_num
      · linarith
    
    -- Show 1/a > 1/sqrt(3)
    have h₆₇ : 1 / a > 1 / Real.sqrt 3 := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · linarith
      
    -- Show 1/sqrt(3) < 1
    have h₆₈ : (1 : ℝ) / Real.sqrt 3 < 1 := by
      have h₆₈₁ : Real.sqrt 3 > 1 := by norm_num [Real.lt_sqrt]
      rw [div_lt_one (by positivity)]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 by norm_num)]
      
    -- Show 1/sqrt(2) < 1
    have h₆₉ : (1 : ℝ) / Real.sqrt 2 < 1 := by
      have h₆₉₁ : Real.sqrt 2 > 1 := by norm_num [Real.lt_sqrt]
      rw [div_lt_one (by positivity)]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      
    have h₆₁₀ : 0 < 1 / a := by positivity
    have h₆₁₁ : 1 / a < 1 := by
      calc
        1 / a < 1 / Real.sqrt 2 := h₆₆
        _ < 1 := h₆₉
        
    rw [Int.floor_eq_iff]
    norm_num at h₆₁₀ h₆₁₁ ⊢
    constructor <;> norm_num <;> linarith
  
  -- Step 4: Derive 1/a = a^2 - 2
  have h₇ : 1 / a = a^2 - 2 := by
    rw [h₆] at h₅
    linarith
  
  -- Step 5: Derive a^3 - 2a - 1 = 0
  have h₈ : a^3 - 2*a - 1 = 0 := by
    have h₈₁ : 1 = a * (a^2 - 2) := by
      field_simp [h₀.ne'] at h₇
      linarith
    nlinarith
  
  -- Step 6: Derive a^2 - a - 1 = 0
  have h₉ : a^2 - a - 1 = 0 := by
    have h₉₁ : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf at h₈ ⊢
      linarith
    have h₉₂ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₉₂
    linarith
  
  -- Step 7: Calculate powers of a using a^2 = a + 1
  have h₉_eq : a^2 = a + 1 := by linarith
  
  have h₁₀ : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [h₉_eq]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h₉_eq]
      _ = 2 * a + 1 := by ring
  
  have h₁₁ : a^6 = 8 * a + 5 := by
    calc
      a^6 = (a^3)^2 := by ring
      _ = (2 * a + 1)^2 := by rw [h₁₀]
      _ = 4 * a^2 + 4 * a + 1 := by ring
      _ = 4 * (a + 1) + 4 * a + 1 := by rw [h₉_eq]
      _ = 8 * a + 5 := by ring
  
  have h₁₂ : a^12 = 144 * a + 89 := by
    calc
      a^12 = (a^6)^2 := by ring
      _ = (8 * a + 5)^2 := by rw [h₁₁]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₉_eq]
      _ = 144 * a + 89 := by ring
  
  -- Step 8: Calculate 1/a
  have h₁₃ : 1 / a = a - 1 := by
    have h₁₃₁ : a^2 - a - 1 = 0 := h₉
    have h₁₃₂ : a ≠ 0 := by linarith
    field_simp [h₁₃₂] at h₁₃₁ ⊢
    nlinarith
  
  -- Step 9: Final Calculation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₁₂, h₁₃]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
