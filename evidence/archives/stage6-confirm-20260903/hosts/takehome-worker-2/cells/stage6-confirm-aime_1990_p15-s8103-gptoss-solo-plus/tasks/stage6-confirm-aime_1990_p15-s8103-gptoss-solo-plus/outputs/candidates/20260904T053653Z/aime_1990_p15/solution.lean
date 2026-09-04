import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by
  -- First we establish the recurrence
  --   a·x^{n+2}+b·y^{n+2} = (x+y)(a·x^{n+1}+b·y^{n+1}) - (x*y)(a·x^{n}+b·y^{n})
  have rec_one :
      a * x^3 + b * y^3 =
        (x + y) * (a * x^2 + b * y^2) - (x * y) * (a * x + b * y) := by
    ring
  have rec_two :
      a * x^4 + b * y^4 =
        (x + y) * (a * x^3 + b * y^3) - (x * y) * (a * x^2 + b * y^2) := by
    ring
  have rec_three :
      a * x^5 + b * y^5 =
        (x + y) * (a * x^4 + b * y^4) - (x * y) * (a * x^3 + b * y^3) := by
    ring
  -- Use the given equalities to turn the recurrences into linear equations
  have h_eq1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    calc
      (x + y) * 7 - (x * y) * 3
          = (x + y) * (a * x^2 + b * y^2) - (x * y) * (a * x + b * y) := by
            simp [h₁, h₀]
      _ = a * x^3 + b * y^3 := by
            simpa [rec_one] using rfl
      _ = 16 := h₂
  have h_eq2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    calc
      (x + y) * 16 - (x * y) * 7
          = (x + y) * (a * x^3 + b * y^3) - (x * y) * (a * x^2 + b * y^2) := by
            simp [h₂, h₁]
      _ = a * x^4 + b * y^4 := by
            simpa [rec_two] using rfl
      _ = 42 := h₃
  -- Introduce abbreviations s = x+y and p = x*y
  set s : ℝ := x + y
  set p : ℝ := x * y
  have h1 : 7 * s - 3 * p = 16 := by
    simpa [s, p, mul_comm, mul_left_comm, mul_assoc] using h_eq1
  have h2 : 16 * s - 7 * p = 42 := by
    simpa [s, p, mul_comm, mul_left_comm, mul_assoc] using h_eq2
  -- Solve the linear system for s and p
  have hs : s = -14 := by
    linarith
  have hp : p = -38 := by
    linarith
  -- Apply the recurrence for n = 3 and substitute the known values
  calc
    a * x^5 + b * y^5
        = s * (a * x^4 + b * y^4) - p * (a * x^3 + b * y^3) := by
          simpa [s, p] using rec_three
    _ = s * 42 - p * 16 := by
          simp [h₃, h₂]
    _ = (-14) * 42 - (-38) * 16 := by
          simp [hs, hp]
    _ = 20 := by
          ring
