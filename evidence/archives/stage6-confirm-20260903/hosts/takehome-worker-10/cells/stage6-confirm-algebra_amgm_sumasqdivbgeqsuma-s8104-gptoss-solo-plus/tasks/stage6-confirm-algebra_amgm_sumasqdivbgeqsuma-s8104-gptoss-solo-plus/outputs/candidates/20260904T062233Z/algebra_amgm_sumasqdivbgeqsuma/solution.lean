import Mathlib

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  --------------------------------------------------------------------
  -- auxiliary lemmas:  x² / y + y ≥ 2*x  for positive x y
  --------------------------------------------------------------------
  have h_ab : a ^ 2 / b + b ≥ 2 * a := by
    have hbpos : 0 < b := hb
    have hbne : (b : ℝ) ≠ 0 := ne_of_gt hbpos
    have h_eq : a ^ 2 / b + b - 2 * a = (a - b) ^ 2 / b := by
      field_simp [hbne] ; ring
    have h_nonneg : 0 ≤ (a - b) ^ 2 / b := by
      have : 0 ≤ (a - b) ^ 2 := by exact sq_nonneg _
      exact div_nonneg this (le_of_lt hbpos)
    have : 0 ≤ a ^ 2 / b + b - 2 * a := by
      simpa [h_eq] using h_nonneg
    linarith

  have h_bc : b ^ 2 / c + c ≥ 2 * b := by
    have hcpos : 0 < c := hc
    have hcne : (c : ℝ) ≠ 0 := ne_of_gt hcpos
    have h_eq : b ^ 2 / c + c - 2 * b = (b - c) ^ 2 / c := by
      field_simp [hcne] ; ring
    have h_nonneg : 0 ≤ (b - c) ^ 2 / c := by
      have : 0 ≤ (b - c) ^ 2 := by exact sq_nonneg _
      exact div_nonneg this (le_of_lt hcpos)
    have : 0 ≤ b ^ 2 / c + c - 2 * b := by
      simpa [h_eq] using h_nonneg
    linarith

  have h_cd : c ^ 2 / d + d ≥ 2 * c := by
    have hdpos : 0 < d := hd
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    have h_eq : c ^ 2 / d + d - 2 * c = (c - d) ^ 2 / d := by
      field_simp [hdne] ; ring
    have h_nonneg : 0 ≤ (c - d) ^ 2 / d := by
      have : 0 ≤ (c - d) ^ 2 := by exact sq_nonneg _
      exact div_nonneg this (le_of_lt hdpos)
    have : 0 ≤ c ^ 2 / d + d - 2 * c := by
      simpa [h_eq] using h_nonneg
    linarith

  have h_da : d ^ 2 / a + a ≥ 2 * d := by
    have hapos : 0 < a := ha
    have ane : (a : ℝ) ≠ 0 := ne_of_gt hapos
    have h_eq : d ^ 2 / a + a - 2 * d = (d - a) ^ 2 / a := by
      field_simp [ane] ; ring
    have h_nonneg : 0 ≤ (d - a) ^ 2 / a := by
      have : 0 ≤ (d - a) ^ 2 := by exact sq_nonneg _
      exact div_nonneg this (le_of_lt hapos)
    have : 0 ≤ d ^ 2 / a + a - 2 * d := by
      simpa [h_eq] using h_nonneg
    linarith

  --------------------------------------------------------------------
  -- Sum the four inequalities
  --------------------------------------------------------------------
  have h_sum :
      (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) ≥
        2 * a + 2 * b + 2 * c + 2 * d := by
    linarith [h_ab, h_bc, h_cd, h_da]

  have h_total :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d) ≥
        2 * (a + b + c + d) := by
    simpa [add_comm, add_left_comm, add_assoc, mul_add, two_mul] using h_sum

  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    linarith

  exact this
