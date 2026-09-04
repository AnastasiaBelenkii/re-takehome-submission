import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- auxiliary inequality: for positive `y`, `x² / y + y ≥ 2 * x`
  have lemma_one (x y : ℝ) (hy : 0 < y) : x ^ 2 / y + y ≥ 2 * x := by
    have hy_ne : (y : ℝ) ≠ 0 := ne_of_gt hy
    have h_nonneg : 0 ≤ (x - y) ^ 2 / y := by
      have : 0 ≤ (x - y) ^ 2 := by
        exact sq_nonneg _
      exact div_nonneg this (le_of_lt hy)
    have h_eq : (x - y) ^ 2 / y = x ^ 2 / y + y - 2 * x := by
      have h_expand : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by
        ring
      calc
        (x - y) ^ 2 / y = (x ^ 2 - 2 * x * y + y ^ 2) / y := by
          simpa [h_expand]
        _ = x ^ 2 / y - 2 * x + y := by
          field_simp [hy_ne]
        _ = x ^ 2 / y + y - 2 * x := by
          ring
    have : x ^ 2 / y + y - 2 * x ≥ 0 := by
      simpa [h_eq] using h_nonneg
    linarith

  have h1 : a ^ 2 / b + b ≥ 2 * a := lemma_one a b hb
  have h2 : b ^ 2 / c + c ≥ 2 * b := lemma_one b c hc
  have h3 : c ^ 2 / d + d ≥ 2 * c := lemma_one c d hd
  have h4 : d ^ 2 / a + a ≥ 2 * d := lemma_one d a ha

  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    linarith [h1, h2, h3, h4]

  exact this
