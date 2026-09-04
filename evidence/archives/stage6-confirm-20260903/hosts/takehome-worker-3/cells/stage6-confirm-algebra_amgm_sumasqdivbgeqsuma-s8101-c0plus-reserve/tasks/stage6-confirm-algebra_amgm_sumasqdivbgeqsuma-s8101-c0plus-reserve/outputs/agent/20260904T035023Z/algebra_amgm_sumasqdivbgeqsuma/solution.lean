import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁_b : 0 < b := h₀.2.1
    have h₁_a : 0 < a := h₀.1
    have h₁_sq : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
    have h₁_exp : a^2 - 2 * a * b + b^2 ≥ 0 := by
      calc
        a^2 - 2 * a * b + b^2 = (a - b)^2 := by ring
        _ ≥ 0 := h₁_sq
    have h₁_ineq : a^2 + b^2 ≥ 2 * a * b := by linarith
    calc
      a^2 / b + b = (a^2 + b^2) / b := by field_simp [h₁_b.ne']
      _ ≥ (2 * a * b) / b := by gcongr
      _ = 2 * a := by field_simp [h₁_b.ne']
  
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂_c : 0 < c := h₀.2.2.1
    have h₂_b : 0 < b := h₀.2.1
    have h₂_sq : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
    have h₂_exp : b^2 - 2 * b * c + c^2 ≥ 0 := by
      calc
        b^2 - 2 * b * c + c^2 = (b - c)^2 := by ring
        _ ≥ 0 := h₂_sq
    have h₂_ineq : b^2 + c^2 ≥ 2 * b * c := by linarith
    calc
      b^2 / c + c = (b^2 + c^2) / c := by field_simp [h₂_c.ne']
      _ ≥ (2 * b * c) / c := by gcongr
      _ = 2 * b := by field_simp [h₂_c.ne']
  
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃_d : 0 < d := h₀.2.2.2
    have h₃_c : 0 < c := h₀.2.2.1
    have h₃_sq : 0 ≤ (c - d)^2 := sq_nonneg (c - d)
    have h₃_exp : c^2 - 2 * c * d + d^2 ≥ 0 := by
      calc
        c^2 - 2 * c * d + d^2 = (c - d)^2 := by ring
        _ ≥ 0 := h₃_sq
    have h₃_ineq : c^2 + d^2 ≥ 2 * c * d := by linarith
    calc
      c^2 / d + d = (c^2 + d^2) / d := by field_simp [h₃_d.ne']
      _ ≥ (2 * c * d) / d := by gcongr
      _ = 2 * c := by field_simp [h₃_d.ne']
  
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄_a : 0 < a := h₀.1
    have h₄_d : 0 < d := h₀.2.2.2
    have h₄_sq : 0 ≤ (d - a)^2 := sq_nonneg (d - a)
    have h₄_exp : d^2 - 2 * d * a + a^2 ≥ 0 := by
      calc
        d^2 - 2 * d * a + a^2 = (d - a)^2 := by ring
        _ ≥ 0 := h₄_sq
    have h₄_ineq : d^2 + a^2 ≥ 2 * d * a := by linarith
    calc
      d^2 / a + a = (d^2 + a^2) / a := by field_simp [h₄_a.ne']
      _ ≥ (2 * d * a) / a := by gcongr
      _ = 2 * d := by field_simp [h₄_a.ne']
  
  linarith
