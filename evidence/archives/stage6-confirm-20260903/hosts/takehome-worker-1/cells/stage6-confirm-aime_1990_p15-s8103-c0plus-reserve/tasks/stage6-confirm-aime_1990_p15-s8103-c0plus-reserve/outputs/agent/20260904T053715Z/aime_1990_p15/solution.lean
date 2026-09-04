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
  -- First we establish the basic recurrence
  --   Sₙ₊₂ = (x+y)·Sₙ₊₁ – (x·y)·Sₙ  where Sₙ = a·xⁿ + b·yⁿ
  have rec₁ : a * x ^ 3 + b * y ^ 3 =
      (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    ring
  have rec₂ : a * x ^ 4 + b * y ^ 4 =
      (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    ring
  have rec₃ : a * x ^ 5 + b * y ^ 5 =
      (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    ring

  -- Using the given equalities we translate the recurrences into linear equations
  have eq1 : 16 = (x + y) * 7 - (x * y) * 3 := by
    simpa [h₀, h₁, h₂] using rec₁
  have eq2 : 42 = (x + y) * 16 - (x * y) * 7 := by
    simpa [h₁, h₂, h₃] using rec₂

  -- From the two linear equations we solve for p = x + y and q = x*y
  have hxy_sum : x + y = -14 := by
    have h1 : 7 * (x + y) - 3 * (x * y) = 16 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq1.symm
    have h2 : 16 * (x + y) - 7 * (x * y) = 42 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq2.symm
    linarith
  have hxy_mul : x * y = -38 := by
    have h1 : 7 * (x + y) - 3 * (x * y) = 16 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq1.symm
    have h2 : 16 * (x + y) - 7 * (x * y) = 42 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq2.symm
    linarith

  -- Finally we compute S₅ using the recurrence and the solved values
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
          simpa using rec₃
    _ = (x + y) * 42 - (x * y) * 16 := by
          simpa [h₂, h₃]
    _ = (-14) * 42 - (-38) * 16 := by
          simpa [hxy_sum, hxy_mul]
    _ = 20 := by
          ring
