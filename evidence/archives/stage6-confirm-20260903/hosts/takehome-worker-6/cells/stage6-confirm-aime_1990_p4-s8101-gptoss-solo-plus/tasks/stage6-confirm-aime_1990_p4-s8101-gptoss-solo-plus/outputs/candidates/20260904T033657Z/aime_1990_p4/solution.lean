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
  set t := x ^ 2 - 10 * x with ht
  have h₁' : t - 29 ≠ 0 := by
    simpa [ht] using h₁
  have h₂' : t - 45 ≠ 0 := by
    simpa [ht] using h₂
  have h₃' : t - 69 ≠ 0 := by
    simpa [ht] using h₃
  -- clear denominators
  have h_eq :
      (t - 45) * (t - 69) + (t - 29) * (t - 69) - 2 * (t - 29) * (t - 45) = 0 := by
    have h := h₄
    field_simp [ht] at h
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
      left_distrib, right_distrib] using h
  -- simplify the numerator
  have h_lin : -64 * t + 2496 = 0 := by
    have : (t - 45) * (t - 69) + (t - 29) * (t - 69) - 2 * (t - 29) * (t - 45) =
        -64 * t + 2496 := by
      ring
    simpa [this] using h_eq
  have ht_eq : t = 39 := by
    linarith [h_lin]
  have hx_quad : x ^ 2 - 10 * x = 39 := by
    simpa [ht] using ht_eq
  have hx_zero : x ^ 2 - 10 * x - 39 = 0 := by
    linarith
  have hfactor : x ^ 2 - 10 * x - 39 = (x - 13) * (x + 3) := by
    ring
  have hprod : (x - 13) * (x + 3) = 0 := by
    simpa [hfactor] using hx_zero
  rcases mul_eq_zero.mp hprod with h13 | hneg3
  · exact sub_eq_zero.mp h13
  · exfalso
    have hx : x = -3 := by
      linarith [hneg3]
    have : (0 : ℝ) < -3 := by
      simpa [hx] using h₀
    linarith
