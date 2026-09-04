import Mathlib

set_option maxHeartbeats 0

open Real

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
  (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
  (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
  a * x ^ 5 + b * y ^ 5 = 20 := by
  -- recurrence for power sums
  have hrec3 :
      a * x ^ 3 + b * y ^ 3 =
        (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    ring
  have hrec4 :
      a * x ^ 4 + b * y ^ 4 =
        (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring
  have hrec5 :
      a * x ^ 5 + b * y ^ 5 =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring

  -- obtain linear equations for p = x + y and q = x*y
  have h_eq1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    have := hrec3
    have := (by
      simpa [h₀, h₁, h₂] using this)
    simpa [eq_comm] using this.symm
  have h_eq2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    have := hrec4
    have := (by
      simpa [h₁, h₂, h₃] using this)
    simpa [eq_comm] using this.symm

  -- solve for p and q
  have hp : x + y = -14 := by
    linarith [h_eq1, h_eq2]
  have hq : x * y = -38 := by
    linarith [h_eq1, h_eq2]

  -- expression for the 5‑th term
  have h5 : a * x ^ 5 + b * y ^ 5 =
        (x + y) * 42 - (x * y) * 16 := by
    simpa [h₃, h₂] using hrec5

  -- substitute p and q and evaluate
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * 42 - (x * y) * 16 := h5
    _ = (-14) * 42 - (-38) * 16 := by
        simpa [hp, hq]
    _ = 20 := by
        norm_num
