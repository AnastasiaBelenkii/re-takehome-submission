import Mathlib

open Real

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
  (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
  (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
  a * x ^ 5 + b * y ^ 5 = 20 := by
  -- recurrence identity for powers
  have hrec3 :
      (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) =
        a * x ^ 3 + b * y ^ 3 := by
    ring
  have hrec4 :
      (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) =
        a * x ^ 4 + b * y ^ 4 := by
    ring
  have hrec5 :
      (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) =
        a * x ^ 5 + b * y ^ 5 := by
    ring
  -- obtain linear equations for x+y and x*y
  have h_eq1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    have := hrec3
    simpa [h₀, h₁, h₂] using this
  have h_eq2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    have := hrec4
    simpa [h₁, h₂, h₃] using this
  -- solve for the sum and product
  have h_sum : x + y = -14 := by
    linarith [h_eq1, h_eq2]
  have h_prod : x * y = -38 := by
    linarith [h_eq1, h_eq2, h_sum]
  -- compute the fifth power sum using the recurrence
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
          simpa using hrec5.symm
    _ = (x + y) * 42 - (x * y) * 16 := by
          simp [h₃, h₂]
    _ = (-14) * 42 - (-38) * 16 := by
          simp [h_sum, h_prod]
    _ = 20 := by
          ring
