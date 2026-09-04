import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
  (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
  (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
  a * x ^ 5 + b * y ^ 5 = 20 := by
  -- recurrence `S_{n+2} = (x+y) S_{n+1} - (x*y) S_n`
  have hrec3 :
      a * x ^ 3 + b * y ^ 3 =
        (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    have hx : x ^ 3 = (x + y) * x ^ 2 - (x * y) * x := by ring
    have hy : y ^ 3 = (x + y) * y ^ 2 - (x * y) * y := by ring
    calc
      a * x ^ 3 + b * y ^ 3
          = a * ((x + y) * x ^ 2 - (x * y) * x) +
            b * ((x + y) * y ^ 2 - (x * y) * y) := by
            simpa [hx, hy]
      _ = (x + y) * (a * x ^ 2 + b * y ^ 2) -
          (x * y) * (a * x + b * y) := by ring
  have hrec4 :
      a * x ^ 4 + b * y ^ 4 =
        (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    have hx : x ^ 4 = (x + y) * x ^ 3 - (x * y) * x ^ 2 := by ring
    have hy : y ^ 4 = (x + y) * y ^ 3 - (x * y) * y ^ 2 := by ring
    calc
      a * x ^ 4 + b * y ^ 4
          = a * ((x + y) * x ^ 3 - (x * y) * x ^ 2) +
            b * ((x + y) * y ^ 3 - (x * y) * y ^ 2) := by
            simpa [hx, hy]
      _ = (x + y) * (a * x ^ 3 + b * y ^ 3) -
          (x * y) * (a * x ^ 2 + b * y ^ 2) := by ring
  have hrec5 :
      a * x ^ 5 + b * y ^ 5 =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    have hx : x ^ 5 = (x + y) * x ^ 4 - (x * y) * x ^ 3 := by ring
    have hy : y ^ 5 = (x + y) * y ^ 4 - (x * y) * y ^ 3 := by ring
    calc
      a * x ^ 5 + b * y ^ 5
          = a * ((x + y) * x ^ 4 - (x * y) * x ^ 3) +
            b * ((x + y) * y ^ 4 - (x * y) * y ^ 3) := by
            simpa [hx, hy]
      _ = (x + y) * (a * x ^ 4 + b * y ^ 4) -
          (x * y) * (a * x ^ 3 + b * y ^ 3) := by ring
  -- Linear equations for `p = x + y` and `q = x * y`.
  have eq1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    simpa [h₂, h₁, h₀] using hrec3.symm
  have eq2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    simpa [h₃, h₂, h₁] using hrec4.symm
  -- Solve the system.
  have hxy : x + y = -14 := by
    have h1 : (7 : ℝ) * (x + y) - 3 * (x * y) = 16 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq1
    have h2 : (16 : ℝ) * (x + y) - 7 * (x * y) = 42 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq2
    linarith
  have hxy_prod : x * y = -38 := by
    have h1 : (7 : ℝ) * (x + y) - 3 * (x * y) = 16 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq1
    have h2 : (16 : ℝ) * (x + y) - 7 * (x * y) = 42 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using eq2
    have : (7 : ℝ) * (-14) - 3 * (x * y) = 16 := by
      simpa [hxy] using h1
    linarith
  -- Compute `S₅`.
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := hrec5
    _ = (x + y) * 42 - (x * y) * 16 := by simpa [h₃, h₂]
    _ = (-14) * 42 - (-38) * 16 := by simpa [hxy, hxy_prod]
    _ = 20 := by ring
