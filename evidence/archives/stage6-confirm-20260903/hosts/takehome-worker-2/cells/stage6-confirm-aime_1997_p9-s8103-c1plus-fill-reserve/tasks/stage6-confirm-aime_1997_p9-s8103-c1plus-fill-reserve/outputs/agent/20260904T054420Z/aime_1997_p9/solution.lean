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
  have h_floor_a2 : Int.floor (a^2) = 2 := by
    have h₄ : (2 : ℝ) ≤ a^2 := by linarith
    have h₅ : a^2 < (3 : ℝ) := by linarith
    norm_num [Int.floor_eq_iff] at h₄ h₅ ⊢
    <;> constructor <;> norm_num <;> linarith
  
  -- Step 2: Determine floor(1/a)
  have h_floor_1a : Int.floor (1 / a) = 0 := by
    have h₆ : a > 1 := by
      nlinarith [sq_pos_of_pos h₀]
    have h₇ : 1 / a < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have h₈ : 1 / a > 0 := by positivity
    norm_num [Int.floor_eq_iff] at h₇ h₈ ⊢
    <;> constructor <;> norm_num <;> linarith
  
  -- Step 3: Establish the relationship 1/a = a^2 - 2
  have h_rel : 1 / a = a^2 - 2 := by
    have h₉ : (1 / a : ℝ) - ↑(Int.floor (1 / a)) = a^2 - ↑(Int.floor (a^2)) := by simpa using h₁
    rw [h_floor_1a, h_floor_a2] at h₉
    ring_nf at h₉ ⊢
    linarith
  
  -- Step 4: Derive the cubic equation a^3 - 2a - 1 = 0
  have h_cubic : a^3 - 2 * a - 1 = 0 := by
    have h₁₀ : a ≠ 0 := by linarith
    field_simp [h₁₀] at h_rel ⊢
    nlinarith
  
  -- Step 5: Factor to find a^2 - a - 1 = 0
  have h_quad : a^2 - a - 1 = 0 := by
    have h₁₁ : (a + 1) * (a^2 - a - 1) = a^3 - 2 * a - 1 := by ring
    rw [h_cubic] at h₁₁
    rw [← mul_zero (a + 1)] at h₁₁
    have h₁₂ : (a + 1 : ℝ) ≠ 0 := by linarith
    apply mul_left_cancel₀ h₁₂
    exact h₁₁
  
  -- Step 6: Solve for a (optional, but useful for understanding)
  -- We actually proceed using the quadratic relation directly to avoid sqrt arithmetic
  -- Step 7: Compute the final value using the relation a^2 = a + 1
  have h_a2 : a^2 = a + 1 := by
    have h₁₉ : a^2 - a - 1 = 0 := h_quad
    linarith
  
  have h_inv_a : 1 / a = a - 1 := by
    have h₂₀ : a ≠ 0 := by linarith
    have h₂₁ : a^2 = a + 1 := h_a2
    field_simp [h₂₀]
    nlinarith
  
  have h_a3 : a^3 = 2 * a + 1 := by
    calc
      a^3 = a^2 * a := by ring
      _ = (a + 1) * a := by rw [h_a2]
      _ = a^2 + a := by ring
      _ = (a + 1) + a := by rw [h_a2]
      _ = 2 * a + 1 := by ring
  
  have h_a4 : a^4 = 3 * a + 2 := by
    calc
      a^4 = a^3 * a := by ring
      _ = (2 * a + 1) * a := by rw [h_a3]
      _ = 2 * a^2 + a := by ring
      _ = 2 * (a + 1) + a := by rw [h_a2]
      _ = 3 * a + 2 := by ring
  
  have h_a5 : a^5 = 5 * a + 3 := by
    calc
      a^5 = a^4 * a := by ring
      _ = (3 * a + 2) * a := by rw [h_a4]
      _ = 3 * a^2 + 2 * a := by ring
      _ = 3 * (a + 1) + 2 * a := by rw [h_a2]
      _ = 5 * a + 3 := by ring
  
  have h_a6 : a^6 = 8 * a + 5 := by
    calc
      a^6 = a^5 * a := by ring
      _ = (5 * a + 3) * a := by rw [h_a5]
      _ = 5 * a^2 + 3 * a := by ring
      _ = 5 * (a + 1) + 3 * a := by rw [h_a2]
      _ = 8 * a + 5 := by ring
  
  have h_a7 : a^7 = 13 * a + 8 := by
    calc
      a^7 = a^6 * a := by ring
      _ = (8 * a + 5) * a := by rw [h_a6]
      _ = 8 * a^2 + 5 * a := by ring
      _ = 8 * (a + 1) + 5 * a := by rw [h_a2]
      _ = 13 * a + 8 := by ring
  
  have h_a8 : a^8 = 21 * a + 13 := by
    calc
      a^8 = a^7 * a := by ring
      _ = (13 * a + 8) * a := by rw [h_a7]
      _ = 13 * a^2 + 8 * a := by ring
      _ = 13 * (a + 1) + 8 * a := by rw [h_a2]
      _ = 21 * a + 13 := by ring
  
  have h_a9 : a^9 = 34 * a + 21 := by
    calc
      a^9 = a^8 * a := by ring
      _ = (21 * a + 13) * a := by rw [h_a8]
      _ = 21 * a^2 + 13 * a := by ring
      _ = 21 * (a + 1) + 13 * a := by rw [h_a2]
      _ = 34 * a + 21 := by ring
  
  have h_a10 : a^10 = 55 * a + 34 := by
    calc
      a^10 = a^9 * a := by ring
      _ = (34 * a + 21) * a := by rw [h_a9]
      _ = 34 * a^2 + 21 * a := by ring
      _ = 34 * (a + 1) + 21 * a := by rw [h_a2]
      _ = 55 * a + 34 := by ring
  
  have h_a11 : a^11 = 89 * a + 55 := by
    calc
      a^11 = a^10 * a := by ring
      _ = (55 * a + 34) * a := by rw [h_a10]
      _ = 55 * a^2 + 34 * a := by ring
      _ = 55 * (a + 1) + 34 * a := by rw [h_a2]
      _ = 89 * a + 55 := by ring
  
  have h_a12 : a^12 = 144 * a + 89 := by
    calc
      a^12 = a^11 * a := by ring
      _ = (89 * a + 55) * a := by rw [h_a11]
      _ = 89 * a^2 + 55 * a := by ring
      _ = 89 * (a + 1) + 55 * a := by rw [h_a2]
      _ = 144 * a + 89 := by ring
  
  calc
    a^12 - 144 * (1 / a) = (144 * a + 89) - 144 * (a - 1) := by
      rw [h_a12, h_inv_a]
    _ = 144 * a + 89 - 144 * a + 144 := by ring
    _ = 89 + 144 := by ring
    _ = 233 := by norm_num
