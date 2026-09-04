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
  -- From h₂ and h₃, we know 2 < a² < 3, so Int.floor(a²) = 2
  have h₄ : Int.floor (a^2) = 2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try linarith) <;>
      (try nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (a^2 - 3)])
  
  -- From h₁ and h₄, we get 1/a - Int.floor(1/a) = a² - 2
  have h₅ : 1 / a - Int.floor (1 / a) = a^2 - 2 := by
    rw [h₄] at h₁
    linarith
  
  -- Since 2 < a² < 3, we have √2 < a < √3, so 1/√3 < 1/a < 1/√2
  -- This means 0 < 1/a < 1, so Int.floor(1/a) = 0
  have h₆ : Int.floor (1 / a) = 0 := by
    have h₆₁ : 0 < 1 / a := by positivity
    have h₆₂ : 1 / a < 1 := by
      have h₆₃ : a > 1 := by
        nlinarith [sq_pos_of_pos h₀]
      have h₆₄ : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      exact h₆₄
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h₆₁ h₆₂ ⊢ <;>
      (try linarith) <;>
      (try nlinarith)
  
  -- Substituting h₆ into h₅ gives us 1/a = a² - 2
  have h₇ : 1 / a = a^2 - 2 := by
    rw [h₆] at h₅
    linarith
  
  -- This gives us the equation a³ - 2a - 1 = 0
  have h₈ : a^3 - 2 * a - 1 = 0 := by
    have h₈₁ : a ≠ 0 := by linarith
    field_simp [h₈₁] at h₇
    nlinarith
  
  -- We can factor: a³ - 2a - 1 = (a+1)(a²-a-1) = 0
  -- Since a > 0, we must have a² - a - 1 = 0
  have h₉ : a^2 - a - 1 = 0 := by
    have h₉₁ : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf at h₈ ⊢
      linarith
    have h₉₂ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₉₂
    linarith
  
  -- From h₉, we have a² = a + 1
  have h₁₀ : a^2 = a + 1 := by linarith
  
  -- Using a² = a + 1, we can compute higher powers recursively
  -- a³ = a·a² = a(a+1) = a² + a = (a+1) + a = 2a + 1
  have h₁₁ : a^3 = 2 * a + 1 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (a + 1) := by rw [h₁₀]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h₁₀]
      _ = 2 * a + 1 := by ring
  
  -- a⁴ = a·a³ = a(2a+1) = 2a² + a = 2(a+1) + a = 3a + 2
  have h₁₂ : a^4 = 3 * a + 2 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2 * a + 1) := by rw [h₁₁]
      _ = 2 * a^2 + a := by ring
      _ = 2 * (a + 1) + a := by rw [h₁₀]
      _ = 3 * a + 2 := by ring
  
  -- Continue computing powers up to a¹²
  have h₁₃ : a^5 = 5 * a + 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (3 * a + 2) := by rw [h₁₂]
      _ = 3 * a^2 + 2 * a := by ring
      _ = 3 * (a + 1) + 2 * a := by rw [h₁₀]
      _ = 5 * a + 3 := by ring
  
  have h₁₄ : a^6 = 8 * a + 5 := by
    calc
      a^6 = a * a^5 := by ring
      _ = a * (5 * a + 3) := by rw [h₁₃]
      _ = 5 * a^2 + 3 * a := by ring
      _ = 5 * (a + 1) + 3 * a := by rw [h₁₀]
      _ = 8 * a + 5 := by ring
  
  have h₁₅ : a^7 = 13 * a + 8 := by
    calc
      a^7 = a * a^6 := by ring
      _ = a * (8 * a + 5) := by rw [h₁₄]
      _ = 8 * a^2 + 5 * a := by ring
      _ = 8 * (a + 1) + 5 * a := by rw [h₁₀]
      _ = 13 * a + 8 := by ring
  
  have h₁₆ : a^8 = 21 * a + 13 := by
    calc
      a^8 = a * a^7 := by ring
      _ = a * (13 * a + 8) := by rw [h₁₅]
      _ = 13 * a^2 + 8 * a := by ring
      _ = 13 * (a + 1) + 8 * a := by rw [h₁₀]
      _ = 21 * a + 13 := by ring
  
  have h₁₇ : a^9 = 34 * a + 21 := by
    calc
      a^9 = a * a^8 := by ring
      _ = a * (21 * a + 13) := by rw [h₁₆]
      _ = 21 * a^2 + 13 * a := by ring
      _ = 21 * (a + 1) + 13 * a := by rw [h₁₀]
      _ = 34 * a + 21 := by ring
  
  have h₁₈ : a^10 = 55 * a + 34 := by
    calc
      a^10 = a * a^9 := by ring
      _ = a * (34 * a + 21) := by rw [h₁₇]
      _ = 34 * a^2 + 21 * a := by ring
      _ = 34 * (a + 1) + 21 * a := by rw [h₁₀]
      _ = 55 * a + 34 := by ring
  
  have h₁₉ : a^11 = 89 * a + 55 := by
    calc
      a^11 = a * a^10 := by ring
      _ = a * (55 * a + 34) := by rw [h₁₈]
      _ = 55 * a^2 + 34 * a := by ring
      _ = 55 * (a + 1) + 34 * a := by rw [h₁₀]
      _ = 89 * a + 55 := by ring
  
  have h₂₀ : a^12 = 144 * a + 89 := by
    calc
      a^12 = a * a^11 := by ring
      _ = a * (89 * a + 55) := by rw [h₁₉]
      _ = 89 * a^2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [h₁₀]
      _ = 144 * a + 89 := by ring
  
  -- Now substitute into the target expression
  have h₂₁ : a^12 - 144 * (1 / a) = 233 := by
    have h₂₁₁ : 1 / a = a^2 - 2 := by rw [h₇]
    calc
      a^12 - 144 * (1 / a) = a^12 - 144 * (a^2 - 2) := by rw [h₂₁₁]
      _ = a^12 - 144 * a^2 + 288 := by ring
      _ = (144 * a + 89) - 144 * a^2 + 288 := by rw [h₂₀]
      _ = 144 * a + 89 - 144 * (a + 1) + 288 := by rw [h₁₀]
      _ = 144 * a + 89 - 144 * a - 144 + 288 := by ring
      _ = 233 := by ring
  
  exact h₂₁
