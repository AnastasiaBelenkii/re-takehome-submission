import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  -- non‑zero denominators
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hd0 : d ≠ 0 := ne_of_gt hd
  -- rewrite each pair using a square
  have h1 : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
    field_simp [hb0] ; ring
  have h2 : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
    field_simp [hc0] ; ring
  have h3 : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
    field_simp [hd0] ; ring
  have h4 : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
    field_simp [ha0] ; ring
  -- combine the equalities
  have h_eq :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d) =
        (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - d) ^ 2 / d + (d - a) ^ 2 / a := by
    calc
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d)
          = (a ^ 2 / b + b - 2 * a) +
            (b ^ 2 / c + c - 2 * b) +
            (c ^ 2 / d + d - 2 * c) +
            (d ^ 2 / a + a - 2 * d) := by ring
      _ = (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - d) ^ 2 / d + (d - a) ^ 2 / a := by
            simpa [h1, h2, h3, h4]
  -- each summand on the right‑hand side is non‑negative
  have h_nonneg :
      0 ≤ (a - b) ^ 2 / b + (b - c) ^ 2 / c + (c - d) ^ 2 / d + (d - a) ^ 2 / a := by
    have h₁ : 0 ≤ (a - b) ^ 2 / b :=
      div_nonneg (pow_two_nonneg (a - b)) (le_of_lt hb)
    have h₂ : 0 ≤ (b - c) ^ 2 / c :=
      div_nonneg (pow_two_nonneg (b - c)) (le_of_lt hc)
    have h₃ : 0 ≤ (c - d) ^ 2 / d :=
      div_nonneg (pow_two_nonneg (c - d)) (le_of_lt hd)
    have h₄ : 0 ≤ (d - a) ^ 2 / a :=
      div_nonneg (pow_two_nonneg (d - a)) (le_of_lt ha)
    have h12 : 0 ≤ (a - b) ^ 2 / b + (b - c) ^ 2 / c := add_nonneg h₁ h₂
    have h34 : 0 ≤ (c - d) ^ 2 / d + (d - a) ^ 2 / a := add_nonneg h₃ h₄
    have h1234 : 0 ≤ ((a - b) ^ 2 / b + (b - c) ^ 2 / c) +
                     ((c - d) ^ 2 / d + (d - a) ^ 2 / a) :=
      add_nonneg h12 h34
    simpa [add_comm, add_left_comm, add_assoc] using h1234
  -- conclude the desired inequality
  have : 0 ≤ a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a - (a + b + c + d) := by
    simpa [h_eq] using h_nonneg
  linarith
