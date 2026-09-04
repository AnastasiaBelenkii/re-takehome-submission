import Mathlib

open Real

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x ^ 2 + b * y ^ 2 = 7)
  (h₂ : a * x ^ 3 + b * y ^ 3 = 16)
  (h₃ : a * x ^ 4 + b * y ^ 4 = 42) :
  a * x ^ 5 + b * y ^ 5 = 20 := by
  -- auxiliary identities for powers
  have h_id1 :
      a * x ^ 3 + b * y ^ 3 =
        (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
    have : a * x ^ 2 * x + b * y ^ 2 * y =
        (x + y) * (a * x ^ 2 + b * y ^ 2) - (x * y) * (a * x + b * y) := by
      ring
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  have h_id2 :
      a * x ^ 4 + b * y ^ 4 =
        (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
    have : a * x ^ 3 * x + b * y ^ 3 * y =
        (x + y) * (a * x ^ 3 + b * y ^ 3) - (x * y) * (a * x ^ 2 + b * y ^ 2) := by
      ring
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  have h_id3 :
      a * x ^ 5 + b * y ^ 5 =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
    have : a * x ^ 4 * x + b * y ^ 4 * y =
        (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := by
      ring
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
  -- obtain linear equations for S = x + y and P = x * y
  have h_eq1 : (x + y) * 7 - (x * y) * 3 = 16 := by
    have h := h₂
    rw [h_id1] at h
    simpa [h₁, h₀] using h
  have h_eq2 : (x + y) * 16 - (x * y) * 7 = 42 := by
    have h := h₃
    rw [h_id2] at h
    simpa [h₂, h₁] using h
  have hS : x + y = -14 := by
    linarith [h_eq1, h_eq2]
  have hP : x * y = -38 := by
    linarith [h_eq1, h_eq2]
  -- compute the desired sum using the identities
  calc
    a * x ^ 5 + b * y ^ 5
        = (x + y) * (a * x ^ 4 + b * y ^ 4) - (x * y) * (a * x ^ 3 + b * y ^ 3) := h_id3
    _ = (-14) * 42 - (-38) * 16 := by
          simpa [hS, hP, h₃, h₂]
    _ = 20 := by norm_num
