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
    constructor <;> norm_num at h₂ h₃ ⊢ <;>
      (try norm_cast) <;>
      (try linarith) <;>
      (try exact_mod_cast h₂) <;>
      (try exact_mod_cast h₃)
  
  -- Step 2: Determine floor(1/a)
  have h₅ : Int.floor (1 / a) = 0 := by
    have h₅₁ : 1 / a < 1 := by
      have h₅₂ : a > 1 := by nlinarith [sq_nonneg (a - 1)]
      rw [div_lt_one (by positivity)]
      nlinarith
    have h₅₃ : 1 / a ≥ 0 := by positivity
    rw [Int.floor_eq_iff]
    constructor <;> norm_num at h₅₁ h₅₃ ⊢ <;>
      (try norm_cast) <;>
      (try linarith)
  
  -- Step 3: Simplify the fractional part equation
  have h₆ : 1 / a = a^2 - 2 := by
    have h₆₁ : 1 / a - Int.floor (1 / a) = a^2 - Int.floor (a^2) := h₁
    rw [h₄, h₅] at h₆₁
    norm_num at h₆₁ ⊢
    linarith
  
  -- Step 4: Derive cubic equation for a
  have h₇ : a^3 = 2 * a + 1 := by
    have h₇₁ : 1 / a = a^2 - 2 := h₆
    have h₇₂ : 1 = a * (a^2 - 2) := by
      field_simp [h₀.ne'] at h₇₁ ⊢
      <;> nlinarith
    nlinarith
  
  -- Step 5: Factor cubic to find quadratic relation
  have h₈ : a^2 = a + 1 := by
    have h₈₁ : a^3 - 2 * a - 1 = 0 := by
      have h₈₂ : a^3 = 2 * a + 1 := h₇
      linarith
    have h₈₃ : (a + 1) * (a^2 - a - 1) = 0 := by
      ring_nf at h₈₁ ⊢
      linarith
    have h₈₄ : a + 1 ≠ 0 := by nlinarith
    have h₈₅ : a^2 - a - 1 = 0 := by
      apply mul_left_cancel₀ h₈₄
      linarith
    linarith
  
  -- Step 6: Compute powers of a using a^2 = a + 1
  have h₉ : a^3 = 2 * a + 1 := h₇ -- Re-state for clarity in chain
  
  have h₁₀ : a^4 = 3 * a + 2 := by
    calc
      a^4 = a * a^3 := by ring
      _ = a * (2 * a + 1) := by rw [h₉]
      _ = 2 * a^2 + a := by ring
      _ = 2 * (a + 1) + a := by rw [h₈]
      _ = 3 * a + 2 := by ring
  
  have h₁₁ : a^5 = 5 * a + 3 := by
    calc
      a^5 = a * a^4 := by ring
      _ = a * (3 * a + 2) := by rw [h₁₀]
      _ = 3 * a^2 + 2 * a := by ring
      _ = 3 * (a + 1) + 2 * a := by rw [h₈]
      _ = 5 * a + 3 := by ring
  
  have h₁₂ : a^6 = 8 * a + 5 := by
    calc
      a^6 = a * a^5 := by ring
      _ = a * (5 * a + 3) := by rw [h₁₁]
      _ = 5 * a^2 + 3 * a := by ring
      _ = 5 * (a + 1) + 3 * a := by rw [h₈]
      _ = 8 * a + 5 := by ring
  
  have h₁₃ : a^7 = 13 * a + 8 := by
    calc
      a^7 = a * a^6 := by ring
      _ = a * (8 * a + 5) := by rw [h₁₂]
      _ = 8 * a^2 + 5 * a := by ring
      _ = 8 * (a + 1) + 5 * a := by rw [h₈]
      _ = 13 * a + 8 := by ring
  
  have h₁₄ : a^8 = 21 * a + 13 := by
    calc
      a^8 = a * a^7 := by ring
      _ = a * (13 * a + 8) := by rw [h₁₃]
      _ = 13 * a^2 + 8 * a := by ring
      _ = 13 * (a + 1) + 8 * a := by rw [h₈]
      _ = 21 * a + 13 := by ring
  
  have h₁₅ : a^9 = 34 * a + 21 := by
    calc
      a^9 = a * a^8 := by ring
      _ = a * (21 * a + 13) := by rw [h₁₄]
      _ = 21 * a^2 + 13 * a := by ring
      _ = 21 * (a + 1) + 13 * a := by rw [h₈]
      _ = 34 * a + 21 := by ring
  
  have h₁₆ : a^10 = 55 * a + 34 := by
    calc
      a^10 = a * a^9 := by ring
      _ = a * (34 * a + 21) := by rw [h₁₅]
      _ = 34 * a^2 + 21 * a := by ring
      _ = 34 * (a + 1) + 21 * a := by rw [h₈]
      _ = 55 * a + 34 := by ring
  
  have h₁₇ : a^11 = 89 * a + 55 := by
    calc
      a^11 = a * a^10 := by ring
      _ = a * (55 * a + 34) := by rw [h₁₆]
      _ = 55 * a^2 + 34 * a := by ring
      _ = 55 * (a + 1) + 34 * a := by rw [h₈]
      _ = 89 * a + 55 := by ring
  
  have h₁₈ : a^12 = 144 * a + 89 := by
    calc
      a^12 = a * a^11 := by ring
      _ = a * (89 * a + 55) := by rw [h₁₇]
      _ = 89 * a^2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [h₈]
      _ = 144 * a + 89 := by ring
  
  -- Step 7: Compute final expression
  have h₁₉ : a^12 - 144 * (1 / a) = 233 := by
    have h₁₉₁ : 1 / a = a^2 - 2 := h₆
    have h₁₉₂ : a^12 = 144 * a + 89 := h₁₈
    have h₁₉₃ : a^2 - 2 = a - 1 := by
      rw [h₈]
      ring
    calc
      a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a^2 - 2) := by
        rw [h₁₉₂, h₁₉₁]
      _ = (144 * a + 89) - 144 * (a - 1) := by
        rw [h₁₉₃]
      _ = 144 * a + 89 - 144 * a + 144 := by ring
      _ = 233 := by ring
  
  exact h₁₉
