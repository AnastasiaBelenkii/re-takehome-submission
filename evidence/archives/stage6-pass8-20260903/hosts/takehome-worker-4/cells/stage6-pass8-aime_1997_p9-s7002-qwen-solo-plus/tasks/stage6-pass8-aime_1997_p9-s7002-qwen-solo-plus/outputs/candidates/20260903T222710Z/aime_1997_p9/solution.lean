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
  -- Step 1: Show that floor(a²) = 2 using h₂ and h₃
  have h₄ : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try norm_cast) <;>
      (try linarith) <;>
      (try assumption)
  
  -- Step 2: Show that floor(1/a) = 0 using bounds on a
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 1 / a < 1 := by
      have h₅₂ : a > 1 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
      have h₅₃ : 0 < a := h₀
      rw [div_lt_one h₅₃]
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ 2 by norm_num)]
    have h₅₄ : 1 / a ≥ 0 := by positivity
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₅₁ h₅₄ ⊢ <;>
      (try norm_cast) <;>
      (try linarith)
  
  -- Step 3: Use h₁ to get 1/a = a² - 2
  have h₆ : 1 / a = a^2 - 2 := by
    rw [h₄, h₅] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- Step 4: Derive a³ - 2a - 1 = 0
  have h₇ : a^3 - 2*a - 1 = 0 := by
    have h₇₁ : a ≠ 0 := by linarith
    field_simp [h₇₁] at h₆
    nlinarith [sq_pos_of_pos h₀]
  
  -- Step 5: Factor to get (a+1)(a²-a-1) = 0, then a² = a + 1
  have h₈ : a^2 = a + 1 := by
    have h₈₁ : (a + 1) * (a^2 - a - 1) = 0 := by
      nlinarith
    have h₈₂ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₈₂
    nlinarith
  
  -- Step 6: Compute a¹² using recurrence aⁿ = Fₙ·a + Fₙ₋₁
  have h₉ : a^12 = 144 * a + 89 := by
    have h₉₁ : a^3 = 2*a + 1 := by
      nlinarith [h₈]
    have h₉₂ : a^4 = 3*a + 2 := by
      calc
        a^4 = a * a^3 := by ring
        _ = a * (2*a + 1) := by rw [h₉₁]
        _ = 2*a^2 + a := by ring
        _ = 2*(a + 1) + a := by rw [h₈]
        _ = 3*a + 2 := by ring
    have h₉₃ : a^6 = 8*a + 5 := by
      calc
        a^6 = (a^3)^2 := by ring
        _ = (2*a + 1)^2 := by rw [h₉₁]
        _ = 4*a^2 + 4*a + 1 := by ring
        _ = 4*(a + 1) + 4*a + 1 := by rw [h₈]
        _ = 8*a + 5 := by ring
    have h₉₄ : a^12 = (a^6)^2 := by ring
    calc
      a^12 = (a^6)^2 := by rw [h₉₄]
      _ = (8*a + 5)^2 := by rw [h₉₃]
      _ = 64*a^2 + 80*a + 25 := by ring
      _ = 64*(a + 1) + 80*a + 25 := by rw [h₈]
      _ = 144*a + 89 := by ring
  
  -- Step 7: Show 1/a = a - 1
  have h₁₀ : 1 / a = a - 1 := by
    have h₁₀₁ : a ≠ 0 := by linarith
    have h₁₀₂ : a^2 - a - 1 = 0 := by
      nlinarith [h₈]
    field_simp [h₁₀₁]
    nlinarith [h₈]
  
  -- Step 8: Final computation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h₉, h₁₀]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
