import Mathlib

open Real

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
  (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
  (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
  a * x ^ 5 + b * y ^ 5 = 20 := by
  -- Define the auxiliary sums p = x + y and q = x * y.
  set p : ℝ := x + y
  set q : ℝ := x * y

  -- Quadratic identities.
  have hx2 : x ^ 2 = p * x - q := by
    dsimp [p, q]
    ring
  have hy2 : y ^ 2 = p * y - q := by
    dsimp [p, q]
    ring

  -- Cubic identities.
  have hx3 : x ^ 3 = p * x ^ 2 - q * x := by
    calc
      x ^ 3 = x * x ^ 2 := by ring
      _ = x * (p * x - q) := by simpa [hx2]
      _ = p * x ^ 2 - q * x := by ring
  have hy3 : y ^ 3 = p * y ^ 2 - q * y := by
    calc
      y ^ 3 = y * y ^ 2 := by ring
      _ = y * (p * y - q) := by simpa [hy2]
      _ = p * y ^ 2 - q * y := by ring

  -- Relation for the third powers.
  have h_eq1 : p * 7 - q * 3 = 16 := by
    have htemp :
        a * x ^ 3 + b * y ^ 3 =
          p * (a * x ^ 2 + b * y ^ 2) - q * (a * x + b * y) := by
      calc
        a * x ^ 3 + b * y ^ 3
            = a * (p * x ^ 2 - q * x) + b * (p * y ^ 2 - q * y) := by
              simpa [hx3, hy3]
        _ = p * (a * x ^ 2 + b * y ^ 2) - q * (a * x + b * y) := by ring
    have htemp' : p * 7 - q * 3 = a * x ^ 3 + b * y ^ 3 := by
      simpa [h₁, h₀] using htemp.symm
    simpa [h₂] using htemp'

  -- Quartic identities.
  have hx4 : x ^ 4 = p * x ^ 3 - q * x ^ 2 := by
    calc
      x ^ 4 = x * x ^ 3 := by ring
      _ = x * (p * x ^ 2 - q * x) := by simpa [hx3]
      _ = p * x ^ 3 - q * x ^ 2 := by ring
  have hy4 : y ^ 4 = p * y ^ 3 - q * y ^ 2 := by
    calc
      y ^ 4 = y * y ^ 3 := by ring
      _ = y * (p * y ^ 2 - q * y) := by simpa [hy3]
      _ = p * y ^ 3 - q * y ^ 2 := by ring

  -- Relation for the fourth powers.
  have h_eq2 : p * 16 - q * 7 = 42 := by
    have htemp :
        a * x ^ 4 + b * y ^ 4 =
          p * (a * x ^ 3 + b * y ^ 3) - q * (a * x ^ 2 + b * y ^ 2) := by
      calc
        a * x ^ 4 + b * y ^ 4
            = a * (p * x ^ 3 - q * x ^ 2) + b * (p * y ^ 3 - q * y ^ 2) := by
              simpa [hx4, hy4]
        _ = p * (a * x ^ 3 + b * y ^ 3) - q * (a * x ^ 2 + b * y ^ 2) := by ring
    have htemp' : p * 16 - q * 7 = a * x ^ 4 + b * y ^ 4 := by
      simpa [h₂, h₁] using htemp.symm
    simpa [h₃] using htemp'

  -- Solve for p and q.
  have hp : p = -14 := by
    linarith [h_eq1, h_eq2]
  have hq : q = -38 := by
    linarith [h_eq1, h_eq2]

  -- Quintic identities.
  have hx5 : x ^ 5 = p * x ^ 4 - q * x ^ 3 := by
    calc
      x ^ 5 = x * x ^ 4 := by ring
      _ = x * (p * x ^ 3 - q * x ^ 2) := by simpa [hx4]
      _ = p * x ^ 4 - q * x ^ 3 := by ring
  have hy5 : y ^ 5 = p * y ^ 4 - q * y ^ 3 := by
    calc
      y ^ 5 = y * y ^ 4 := by ring
      _ = y * (p * y ^ 3 - q * y ^ 2) := by simpa [hy4]
      _ = p * y ^ 4 - q * y ^ 3 := by ring

  have h5 :
      a * x ^ 5 + b * y ^ 5 =
        p * (a * x ^ 4 + b * y ^ 4) - q * (a * x ^ 3 + b * y ^ 3) := by
    calc
      a * x ^ 5 + b * y ^ 5
          = a * (p * x ^ 4 - q * x ^ 3) + b * (p * y ^ 4 - q * y ^ 3) := by
            simpa [hx5, hy5]
      _ = p * (a * x ^ 4 + b * y ^ 4) - q * (a * x ^ 3 + b * y ^ 3) := by ring

  -- Final computation.
  calc
    a * x ^ 5 + b * y ^ 5
        = p * 42 - q * 16 := by
          simpa [h₃, h₂] using h5
    _ = (-14) * 42 - (-38) * 16 := by
          simp [hp, hq]
    _ = 20 := by ring
