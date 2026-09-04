import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- auxiliary lemmas: each term satisfies an AM‑GM type inequality
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    have hbpos : 0 < b := hb
    have h_eq :
        a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp [hbpos.ne']
      ring
    have h_nonneg : 0 ≤ (a - b) ^ 2 / b := by
      have : 0 ≤ (a - b) ^ 2 := by
        exact pow_two_nonneg (a - b)
      exact div_nonneg this (le_of_lt hbpos)
    have : 0 ≤ a ^ 2 / b + b - 2 * a := by
      simpa [h_eq] using h_nonneg
    linarith
  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    have hcpos : 0 < c := hc
    have h_eq :
        b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp [hcpos.ne']
      ring
    have h_nonneg : 0 ≤ (b - c) ^ 2 / c := by
      have : 0 ≤ (b - c) ^ 2 := by
        exact pow_two_nonneg (b - c)
      exact div_nonneg this (le_of_lt hcpos)
    have : 0 ≤ b ^ 2 / c + c - 2 * b := by
      simpa [h_eq] using h_nonneg
    linarith
  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    have hdpos : 0 < d := hd
    have h_eq :
        c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp [hdpos.ne']
      ring
    have h_nonneg : 0 ≤ (c - d) ^ 2 / d := by
      have : 0 ≤ (c - d) ^ 2 := by
        exact pow_two_nonneg (c - d)
      exact div_nonneg this (le_of_lt hdpos)
    have : 0 ≤ c ^ 2 / d + d - 2 * c := by
      simpa [h_eq] using h_nonneg
    linarith
  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    have hapos : 0 < a := ha
    have h_eq :
        d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp [hapos.ne']
      ring
    have h_nonneg : 0 ≤ (d - a) ^ 2 / a := by
      have : 0 ≤ (d - a) ^ 2 := by
        exact pow_two_nonneg (d - a)
      exact div_nonneg this (le_of_lt hapos)
    have : 0 ≤ d ^ 2 / a + a - 2 * d := by
      simpa [h_eq] using h_nonneg
    linarith

  -- rewrite each inequality as a lower bound for the single fraction
  have h₁' : a ^ 2 / b ≥ 2 * a - b := by linarith
  have h₂' : b ^ 2 / c ≥ 2 * b - c := by linarith
  have h₃' : c ^ 2 / d ≥ 2 * c - d := by linarith
  have h₄' : d ^ 2 / a ≥ 2 * d - a := by linarith

  -- sum the four lower bounds
  have hsum :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a
        ≥ (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
    linarith

  -- simplify the right‑hand side
  have hrhs : (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) = a + b + c + d := by
    ring

  -- conclude
  simpa [hrhs] using hsum
