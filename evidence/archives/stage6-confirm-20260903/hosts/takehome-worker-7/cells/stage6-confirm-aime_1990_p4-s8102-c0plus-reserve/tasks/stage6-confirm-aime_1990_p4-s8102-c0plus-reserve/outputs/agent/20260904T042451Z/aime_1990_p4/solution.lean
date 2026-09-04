import Mathlib

set_option maxHeartbeats 0

open Real

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x ^ 2 - 10 * x - 29 ≠ 0)
  (h₂ : x ^ 2 - 10 * x - 45 ≠ 0)
  (h₃ : x ^ 2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x ^ 2 - 10 * x - 29) + 1 / (x ^ 2 - 10 * x - 45) -
        2 / (x ^ 2 - 10 * x - 69) = 0) :
  x = 13 := by
  -- introduce a simpler notation
  let t : ℝ := x ^ 2 - 10 * x
  have h_eq : 1 / (t - 29) + 1 / (t - 45) - 2 / (t - 69) = 0 := by
    simpa [t] using h₄
  -- non‑zero denominators
  have hden₁ : t - 29 ≠ 0 := by
    simpa [t] using h₁
  have hden₂ : t - 45 ≠ 0 := by
    simpa [t] using h₂
  have hden₃ : t - 69 ≠ 0 := by
    simpa [t] using h₃
  -- clear denominators
  have h_num :
      (t - 45) * (t - 69) + (t - 29) * (t - 69) - 2 * (t - 29) * (t - 45) = 0 := by
    have h := h_eq
    field_simp [hden₁, hden₂, hden₃] at h
    -- now `h` is `((t - 45) + (t - 29)) * (t - 69) - 2 * (t - 29) * (t - 45) = 0`
    simpa [add_comm, add_left_comm, add_assoc, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  -- obtain a linear equation in `t`
  have h_lin : 64 * t = 2496 := by
    have h := h_num
    ring_nf at h
    linarith
  -- solve for `t`
  have ht : t = 39 := by
    have h64 : (64 : ℝ) ≠ 0 := by norm_num
    have : t = 2496 / 64 := (eq_div_iff_mul_eq h64).mpr (by
      simpa [mul_comm] using h_lin)
    norm_num at this
    simpa using this
  -- translate back to a quadratic equation for `x`
  have h_quad : x ^ 2 - 10 * x - 39 = 0 := by
    have : x ^ 2 - 10 * x = 39 := by
      simpa [t] using ht
    linarith
  -- factor the quadratic
  have h_factor : (x - 13) * (x + 3) = 0 := by
    have h_eq' : x ^ 2 - 10 * x - 39 = (x - 13) * (x + 3) := by
      ring
    simpa [h_eq'] using h_quad
  -- the two possible solutions
  have hx : x = 13 ∨ x = -3 := by
    rcases (mul_eq_zero.mp h_factor) with h | h
    · left; linarith
    · right; linarith
  -- discard the negative one using positivity
  cases hx with
  | inl h13 => exact h13
  | inr hneg =>
    exfalso
    have : (0 : ℝ) < -3 := by
      simpa [hneg] using h₀
    linarith
