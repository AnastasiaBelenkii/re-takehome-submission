import Mathlib

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
  -- set `t = x^2 - 10*x`
  let t : ℝ := x ^ 2 - 10 * x
  have h_eq_t : 1 / (t - 29) + 1 / (t - 45) - 2 / (t - 69) = 0 := by
    simpa [t] using h₄
  have h₁' : t - 29 ≠ 0 := by
    simpa [t] using h₁
  have h₂' : t - 45 ≠ 0 := by
    simpa [t] using h₂
  have h₃' : t - 69 ≠ 0 := by
    simpa [t] using h₃
  -- clear denominators and obtain a linear equation in `t`
  have h_lin : -64 * t + 2496 = 0 := by
    have h := h_eq_t
    field_simp [h₁', h₂', h₃'] at h
    -- after `field_simp` we have an expression of the form
    -- `(t - 45 + (t - 29)) * (t - 69) - (t - 29) * (t - 45) * 2 = 0`
    have h_eq :
        (t - 45 + (t - 29)) * (t - 69) - (t - 29) * (t - 45) * 2 = -64 * t + 2496 := by
      ring
    simpa [h_eq] using h
  -- solve for `t`
  have h_t : t = 39 := by
    linarith [h_lin]
  -- translate back to a quadratic equation for `x`
  have hx_quad : x ^ 2 - 10 * x - 39 = 0 := by
    have : x ^ 2 - 10 * x = 39 := by
      simpa [t] using h_t
    linarith
  -- factor the quadratic
  have hx_factor : (x - 13) * (x + 3) = 0 := by
    have h_eq : (x - 13) * (x + 3) = x ^ 2 - 10 * x - 39 := by
      ring
    simpa [h_eq] using hx_quad
  -- analyse the two possibilities
  rcases mul_eq_zero.mp hx_factor with h13 | hneg
  · -- first factor zero gives the desired result
    exact sub_eq_zero.mp h13
  · -- second factor zero contradicts positivity of `x`
    have : x = -3 := by
      have : x + 3 = 0 := hneg
      linarith
    have : False := by
      have : (0 : ℝ) < x := h₀
      linarith
    exact (False.elim this)
