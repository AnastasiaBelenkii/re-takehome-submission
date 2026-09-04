import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  have h₁ : a^2 / b + b ≥ 2 * a := by
    have h₁_sq : (a - b)^2 ≥ 0 := by nlinarith
    have h₁_div : (a - b)^2 / b ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (a - b)
      · linarith
    calc
      a^2 / b + b = (a^2 - 2*a*b + b^2) / b + 2*a := by
        field_simp [hb.ne']
        ring
      _ = (a - b)^2 / b + 2*a := by ring
      _ ≥ 0 + 2*a := by gcongr
      _ = 2*a := by ring
  have h₂ : b^2 / c + c ≥ 2 * b := by
    have h₂_sq : (b - c)^2 ≥ 0 := by nlinarith
    have h₂_div : (b - c)^2 / c ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (b - c)
      · linarith
    calc
      b^2 / c + c = (b^2 - 2*b*c + c^2) / c + 2*b := by
        field_simp [hc.ne']
        ring
      _ = (b - c)^2 / c + 2*b := by ring
      _ ≥ 0 + 2*b := by gcongr
      _ = 2*b := by ring
  have h₃ : c^2 / d + d ≥ 2 * c := by
    have h₃_sq : (c - d)^2 ≥ 0 := by nlinarith
    have h₃_div : (c - d)^2 / d ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (c - d)
      · linarith
    calc
      c^2 / d + d = (c^2 - 2*c*d + d^2) / d + 2*c := by
        field_simp [hd.ne']
        ring
      _ = (c - d)^2 / d + 2*c := by ring
      _ ≥ 0 + 2*c := by gcongr
      _ = 2*c := by ring
  have h₄ : d^2 / a + a ≥ 2 * d := by
    have h₄_sq : (d - a)^2 ≥ 0 := by nlinarith
    have h₄_div : (d - a)^2 / a ≥ 0 := by
      apply div_nonneg
      · exact sq_nonneg (d - a)
      · linarith
    calc
      d^2 / a + a = (d^2 - 2*d*a + a^2) / a + 2*d := by
        field_simp [ha.ne']
        ring
      _ = (d - a)^2 / a + 2*d := by ring
      _ ≥ 0 + 2*d := by gcongr
      _ = 2*d := by ring
  calc
    a^2 / b + b^2 / c + c^2 / d + d^2 / a 
      = (a^2 / b + b) + (b^2 / c + c) + (c^2 / d + d) + (d^2 / a + a) - (a + b + c + d) := by ring
    _ ≥ 2*a + 2*b + 2*c + 2*d - (a + b + c + d) := by
      gcongr <;> assumption
    _ = a + b + c + d := by ring
