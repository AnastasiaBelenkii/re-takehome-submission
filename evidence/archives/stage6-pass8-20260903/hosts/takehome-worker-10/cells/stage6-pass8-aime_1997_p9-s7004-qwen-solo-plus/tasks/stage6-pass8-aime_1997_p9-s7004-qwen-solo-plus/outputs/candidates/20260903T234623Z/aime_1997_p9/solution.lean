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
  -- From h₂ and h₃, we know 2 < a² < 3, so ⌊a²⌋ = 2
  have h₄ : Int.floor (a^2) = 2 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try linarith) <;>
      (try nlinarith [sq_nonneg (a^2 - 2), sq_nonneg (a^2 - 3)])
  
  -- From h₂ and h₃, we get bounds on a: √2 < a < √3
  have h₅ : Real.sqrt 2 < a := by
    have : 0 < a := h₀
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), h₂]
  
  have h₆ : a < Real.sqrt 3 := by
    have : 0 < a := h₀
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    nlinarith [Real.sq_sqrt (show 0 ≤ 3 by norm_num), h₃]
  
  -- This gives us bounds on 1/a: 1/√3 < 1/a < 1/√2
  have h₇ : 1 / a < 1 := by
    have : a > 1 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    rw [div_lt_one (by positivity)]
    nlinarith
  
  have h₈ : 0 < 1 / a := by positivity
  
  -- So ⌊1/a⌋ = 0
  have h₉ : Int.floor (1 / a) = 0 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num at h₇ h₈ ⊢ <;>
      (try linarith) <;>
      (try nlinarith [Real.sq_sqrt (show 0 ≤ 2 by norm_num), Real.sq_sqrt (show 0 ≤ 3 by norm_num)])
  
  -- From h₁, we get 1/a = a² - 2
  have h₁₀ : 1 / a = a^2 - 2 := by
    rw [h₉] at h₁
    rw [h₄] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- This gives us a³ - 2a - 1 = 0
  have h₁₁ : a^3 - 2*a - 1 = 0 := by
    have : a ≠ 0 := by linarith
    field_simp [this] at h₁₀
    ring_nf at h₁₀ ⊢
    nlinarith
  
  -- Factor: (a+1)(a²-a-1) = 0, and since a > 0, we have a² - a - 1 = 0
  have h₁₂ : a^2 - a - 1 = 0 := by
    have : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf at h₁₁ ⊢
      linarith
    have : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ this
    linarith
  
  -- We can use this to compute higher powers of a
  have h₁₃ : a^2 = a + 1 := by linarith
  
  -- Compute a^12 using the recurrence
  have h₁₄ : a^12 = 144 * a + 89 := by
    have h₁₄₁ : a^3 = 2*a + 1 := by
      calc
        a^3 = a * a^2 := by ring
        _ = a * (a + 1) := by rw [h₁₃]
        _ = a^2 + a := by ring
        _ = (a + 1) + a := by rw [h₁₃]
        _ = 2*a + 1 := by ring
    
    have h₁₄₂ : a^4 = 3*a + 2 := by
      calc
        a^4 = a * a^3 := by ring
        _ = a * (2*a + 1) := by rw [h₁₄₁]
        _ = 2*a^2 + a := by ring
        _ = 2*(a + 1) + a := by rw [h₁₃]
        _ = 3*a + 2 := by ring
    
    have h₁₄₃ : a^5 = 5*a + 3 := by
      calc
        a^5 = a * a^4 := by ring
        _ = a * (3*a + 2) := by rw [h₁₄₂]
        _ = 3*a^2 + 2*a := by ring
        _ = 3*(a + 1) + 2*a := by rw [h₁₃]
        _ = 5*a + 3 := by ring
    
    have h₁₄₄ : a^6 = 8*a + 5 := by
      calc
        a^6 = a * a^5 := by ring
        _ = a * (5*a + 3) := by rw [h₁₄₃]
        _ = 5*a^2 + 3*a := by ring
        _ = 5*(a + 1) + 3*a := by rw [h₁₃]
        _ = 8*a + 5 := by ring
    
    have h₁₄₅ : a^7 = 13*a + 8 := by
      calc
        a^7 = a * a^6 := by ring
        _ = a * (8*a + 5) := by rw [h₁₄₄]
        _ = 8*a^2 + 5*a := by ring
        _ = 8*(a + 1) + 5*a := by rw [h₁₃]
        _ = 13*a + 8 := by ring
    
    have h₁₄₆ : a^8 = 21*a + 13 := by
      calc
        a^8 = a * a^7 := by ring
        _ = a * (13*a + 8) := by rw [h₁₄₅]
        _ = 13*a^2 + 8*a := by ring
        _ = 13*(a + 1) + 8*a := by rw [h₁₃]
        _ = 21*a + 13 := by ring
    
    have h₁₄₇ : a^9 = 34*a + 21 := by
      calc
        a^9 = a * a^8 := by ring
        _ = a * (21*a + 13) := by rw [h₁₄₆]
        _ = 21*a^2 + 13*a := by ring
        _ = 21*(a + 1) + 13*a := by rw [h₁₃]
        _ = 34*a + 21 := by ring
    
    have h₁₄₈ : a^10 = 55*a + 34 := by
      calc
        a^10 = a * a^9 := by ring
        _ = a * (34*a + 21) := by rw [h₁₄₇]
        _ = 34*a^2 + 21*a := by ring
        _ = 34*(a + 1) + 21*a := by rw [h₁₃]
        _ = 55*a + 34 := by ring
    
    have h₁₄₉ : a^11 = 89*a + 55 := by
      calc
        a^11 = a * a^10 := by ring
        _ = a * (55*a + 34) := by rw [h₁₄₈]
        _ = 55*a^2 + 34*a := by ring
        _ = 55*(a + 1) + 34*a := by rw [h₁₃]
        _ = 89*a + 55 := by ring
    
    calc
      a^12 = a * a^11 := by ring
      _ = a * (89*a + 55) := by rw [h₁₄₉]
      _ = 89*a^2 + 55*a := by ring
      _ = 89*(a + 1) + 55*a := by rw [h₁₃]
      _ = 144*a + 89 := by ring
  
  -- Now compute a^12 - 144/a
  have h₁₅ : a^12 - 144 * (1 / a) = 233 := by
    have h₁₅₁ : 1 / a = a^2 - 2 := h₁₀
    calc
      a^12 - 144 * (1 / a) = a^12 - 144 * (a^2 - 2) := by rw [h₁₅₁]
      _ = a^12 - 144 * a^2 + 288 := by ring
      _ = (144 * a + 89) - 144 * a^2 + 288 := by rw [h₁₄]
      _ = 144 * a + 89 - 144 * a^2 + 288 := by ring
      _ = 144 * a + 377 - 144 * a^2 := by ring
      _ = 144 * a + 377 - 144 * (a + 1) := by rw [h₁₃]
      _ = 144 * a + 377 - 144 * a - 144 := by ring
      _ = 233 := by ring
  
  exact h₁₅
