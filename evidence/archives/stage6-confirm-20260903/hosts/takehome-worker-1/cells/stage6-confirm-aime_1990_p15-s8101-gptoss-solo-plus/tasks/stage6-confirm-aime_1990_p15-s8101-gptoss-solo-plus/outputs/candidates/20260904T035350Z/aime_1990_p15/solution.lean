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
  -- recurrence for the weighted power sums
  have hrec₁ :
      a * x ^ 3 + b * y ^ 3 =
        (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    ring
  have hrec₂ :
      a * x ^ 4 + b * y ^ 4 =
        (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring
  have hrec₃ :
      a * x ^ 5 + b * y ^ 5 =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring
  -- obtain linear equations for p = x + y and q = x * y
  have h_eq1' :
      (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) = 16 := by
    simpa [h₂] using hrec₁.symm
  have h_eq1 : 7 * (x + y) - 3 * (x * y) = 16 := by
    simpa [h₁, h₀, mul_comm, mul_left_comm, mul_assoc] using h_eq1'
  have h_eq2' :
      (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) = 42 := by
    simpa [h₃] using hrec₂.symm
  have h_eq2 : 16 * (x + y) - 7 * (x * y) = 42 := by
    simpa [h₂, h₁, mul_comm, mul_left_comm, mul_assoc] using h_eq2'
  -- solve for p and q
  have h_p : x + y = -14 := by
    linarith [h_eq1, h_eq2]
  have h_q : x * y = -38 := by
    linarith [h_eq1, h_eq2]
  -- compute the desired sum using the recurrence
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
          simpa using hrec₃
    _ = (x + y) * 42 - (x * y) * 16 := by
          simpa [h₃, h₂]
    _ = (-14) * 42 - (-38) * 16 := by
          simpa [h_p, h_q]
    _ = 20 := by
          ring
