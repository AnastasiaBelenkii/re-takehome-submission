import Mathlib

set_option maxHeartbeats 0

open Real

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩

  -- Helper lemma: `x ^ 2 / y + y ≥ 2 * x` for positive `x, y`.
  have h_one (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
      x ^ 2 / y + y ≥ 2 * x := by
    have hy₀ : y ≠ 0 := ne_of_gt hy
    have h_eq :
        x ^ 2 / y + y - 2 * x = (x - y) ^ 2 / y := by
      field_simp [hy₀]
      ring
    have h_nonneg : 0 ≤ (x - y) ^ 2 / y := by
      have h_sq : 0 ≤ (x - y) ^ 2 := by
        have : (x - y) ^ 2 = (x - y) * (x - y) := by ring
        simpa [this] using mul_self_nonneg (x - y)
      exact div_nonneg h_sq (le_of_lt hy)
    have : 0 ≤ x ^ 2 / y + y - 2 * x := by
      simpa [h_eq] using h_nonneg
    linarith

  -- Apply the helper to each cyclic pair.
  have h₁ : a ^ 2 / b + b ≥ 2 * a := h_one a b ha hb
  have h₂ : b ^ 2 / c + c ≥ 2 * b := h_one b c hb hc
  have h₃ : c ^ 2 / d + d ≥ 2 * c := h_one c d hc hd
  have h₄ : d ^ 2 / a + a ≥ 2 * d := h_one d a hd ha

  -- Rearrange each inequality.
  have h₁' : a ^ 2 / b ≥ 2 * a - b := by linarith
  have h₂' : b ^ 2 / c ≥ 2 * b - c := by linarith
  have h₃' : c ^ 2 / d ≥ 2 * c - d := by linarith
  have h₄' : d ^ 2 / a ≥ 2 * d - a := by linarith

  -- Sum the four lower bounds.
  have hsum :
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a
        ≥ (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) := by
    have := add_le_add (add_le_add h₁' h₂') (add_le_add h₃' h₄')
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using this

  -- Simplify the right‑hand side.
  have hrhs :
      (2 * a - b) + (2 * b - c) + (2 * c - d) + (2 * d - a) = a + b + c + d := by
    ring

  -- Conclude the desired inequality.
  have : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    simpa [hrhs] using hsum
  exact this
