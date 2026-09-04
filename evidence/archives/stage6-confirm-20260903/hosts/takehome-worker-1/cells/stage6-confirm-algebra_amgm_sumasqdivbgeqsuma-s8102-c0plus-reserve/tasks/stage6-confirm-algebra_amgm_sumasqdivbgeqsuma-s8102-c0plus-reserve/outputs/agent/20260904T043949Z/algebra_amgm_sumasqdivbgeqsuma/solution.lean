import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- auxiliary lemma: for positive x y,  x^2 / y + y ≥ 2*x
  have aux (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      x ^ 2 / y + y ≥ 2 * x := by
    have hyne : y ≠ 0 := hy.ne'
    have h_eq : x ^ 2 / y + y - 2 * x = (x - y) ^ 2 / y := by
      field_simp [hyne] ; ring
    have h_nonneg : (x - y) ^ 2 / y ≥ 0 := by
      have : (x - y) ^ 2 ≥ 0 := by
        exact pow_two_nonneg _
      exact div_nonneg this (le_of_lt hy)
    have : x ^ 2 / y + y - 2 * x ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  have h1 : a ^ 2 / b + b ≥ 2 * a := aux a b ha hb
  have h2 : b ^ 2 / c + c ≥ 2 * b := aux b c hb hc
  have h3 : c ^ 2 / d + d ≥ 2 * c := aux c d hc hd
  have h4 : d ^ 2 / a + a ≥ 2 * d := aux d a hd ha

  -- sum the four inequalities
  have hsum : (a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a) + (a + b + c + d) ≥
      2 * (a + b + c + d) := by
    have h12 : a ^ 2 / b + b + (b ^ 2 / c + c) ≥ 2 * a + 2 * b :=
      add_le_add h1 h2
    have h34 : c ^ 2 / d + d + (d ^ 2 / a + a) ≥ 2 * c + 2 * d :=
      add_le_add h3 h4
    have htotal := add_le_add h12 h34
    simpa [add_comm, add_left_comm, add_assoc, two_mul, mul_add, add_mul] using htotal

  -- deduce the desired inequality
  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    linarith
  exact this
