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
  -- Step 1: Show that Int.floor(a^2) = 2 using h₂ and h₃
  have h_floor_a2 : Int.floor (a^2) = 2 := by
    rw [Int.floor_eq_iff]
    norm_num at h₂ h₃ ⊢
    constructor <;> linarith
  
  -- Step 2: Show that Int.floor(1/a) = 0 using bounds on a
  have h_floor_one_over_a : Int.floor (1 / a) = 0 := by
    have h₄ : 1 / a < 1 := by
      have h₄₁ : a > 1 := by
        nlinarith
      have h₄₂ : 1 / a < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
      exact h₄₂
    have h₅ : 0 < 1 / a := by positivity
    rw [Int.floor_eq_iff]
    norm_num at h₄ h₅ ⊢
    constructor <;> linarith
  
  -- Step 3: Substitute floor values into h₁ to get 1/a = a^2 - 2
  have h_eq : 1 / a = a^2 - 2 := by
    rw [h_floor_a2, h_floor_one_over_a] at h₁
    ring_nf at h₁ ⊢
    linarith
  
  -- Step 4: Derive that a satisfies a^3 - 2*a - 1 = 0
  have h_poly : a^3 - 2 * a - 1 = 0 := by
    have h₄ : a ≠ 0 := by linarith
    field_simp [h₄] at h_eq
    ring_nf at h_eq ⊢
    nlinarith
  
  -- Step 5: Factor polynomial to get (a+1)(a^2-a-1) = 0
  have h_factor : (a + 1) * (a^2 - a - 1) = 0 := by
    have h₄ : a^3 - 2 * a - 1 = (a + 1) * (a^2 - a - 1) := by ring
    rw [h₄] at h_poly
    linarith
  
  -- Step 6: Show a^2 - a - 1 = 0 (since a + 1 ≠ 0)
  have h_quad : a^2 - a - 1 = 0 := by
    have h₄ : a + 1 ≠ 0 := by linarith
    apply mul_left_cancel₀ h₄
    linarith
  
  -- Step 7: Use a^2 = a + 1 to compute higher powers
  have h_a2 : a^2 = a + 1 := by linarith
  
  -- Step 8: Compute a^12 using the recurrence relation
  have h_a12 : a^12 = 144 * a + 89 := by
    have h₄ : a^2 = a + 1 := h_a2
    have h₅ : a^3 = 2 * a + 1 := by
      calc
        a^3 = a * a^2 := by ring
        _ = a * (a + 1) := by rw [h₄]
        _ = a^2 + a := by ring
        _ = (a + 1) + a := by rw [h₄]
        _ = 2 * a + 1 := by ring
    have h₆ : a^4 = 3 * a + 2 := by
      calc
        a^4 = a * a^3 := by ring
        _ = a * (2 * a + 1) := by rw [h₅]
        _ = 2 * a^2 + a := by ring
        _ = 2 * (a + 1) + a := by rw [h₄]
        _ = 3 * a + 2 := by ring
    have h₇ : a^5 = 5 * a + 3 := by
      calc
        a^5 = a * a^4 := by ring
        _ = a * (3 * a + 2) := by rw [h₆]
        _ = 3 * a^2 + 2 * a := by ring
        _ = 3 * (a + 1) + 2 * a := by rw [h₄]
        _ = 5 * a + 3 := by ring
    have h₈ : a^6 = 8 * a + 5 := by
      calc
        a^6 = a * a^5 := by ring
        _ = a * (5 * a + 3) := by rw [h₇]
        _ = 5 * a^2 + 3 * a := by ring
        _ = 5 * (a + 1) + 3 * a := by rw [h₄]
        _ = 8 * a + 5 := by ring
    have h₉ : a^12 = (a^6)^2 := by ring
    rw [h₉]
    calc
      (a^6)^2 = (8 * a + 5)^2 := by rw [h₈]
      _ = 64 * a^2 + 80 * a + 25 := by ring
      _ = 64 * (a + 1) + 80 * a + 25 := by rw [h₄]
      _ = 144 * a + 89 := by ring
  
  -- Step 9: Compute 1/a from a^2 - a - 1 = 0
  have h_one_over_a : 1 / a = a - 1 := by
    have h₄ : a ≠ 0 := by linarith
    have h₅ : a^2 - a - 1 = 0 := h_quad
    have h₆ : a^2 = a + 1 := by linarith
    have h₇ : a * (a - 1) = 1 := by
      calc
        a * (a - 1) = a^2 - a := by ring
        _ = 1 := by linarith
    field_simp [h₄]
    linarith
  
  -- Step 10: Final computation
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h_a12, h_one_over_a]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 233 := by ring
