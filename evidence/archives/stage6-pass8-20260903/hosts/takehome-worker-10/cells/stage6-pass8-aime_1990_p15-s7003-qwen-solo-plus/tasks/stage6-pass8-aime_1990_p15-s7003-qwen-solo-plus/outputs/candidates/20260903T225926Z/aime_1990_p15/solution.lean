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
  let P := x + y
  let Q := x * y
  
  have h_rec3 : a * x^3 + b * y^3 = P * (a * x^2 + b * y^2) - Q * (a * x + b * y) := by
    calc
      a * x^3 + b * y^3 = a * x * x^2 + b * y * y^2 := by ring
      _ = a * x * (P * x - Q) + b * y * (P * y - Q) := by
        rw [show x^2 = P * x - Q by ring]
        rw [show y^2 = P * y - Q by ring]
      _ = P * (a * x^2 + b * y^2) - Q * (a * x + b * y) := by ring

  have h_rec4 : a * x^4 + b * y^4 = P * (a * x^3 + b * y^3) - Q * (a * x^2 + b * y^2) := by
    calc
      a * x^4 + b * y^4 = a * x^2 * x^2 + b * y^2 * y^2 := by ring
      _ = a * x^2 * (P * x - Q) + b * y^2 * (P * y - Q) := by
        rw [show x^2 = P * x - Q by ring]
        rw [show y^2 = P * y - Q by ring]
      _ = P * (a * x^3 + b * y^3) - Q * (a * x^2 + b * y^2) := by ring

  have h_PQ1 : P * 7 - Q * 3 = 16 := by
    rw [h_rec3] at h₂
    rw [h₁, h₀] at h₂
    exact h₂

  have h_PQ2 : P * 16 - Q * 7 = 42 := by
    rw [h_rec4] at h₃
    rw [h₂, h₁] at h₃
    exact h₃

  have h_P : P = -14 := by
    have h : P = -14 := by
      linarith [h_PQ1, h_PQ2]
    exact h

  have h_Q : Q = -38 := by
    have h : Q = -38 := by
      linarith [h_PQ1, h_PQ2, h_P]
    exact h

  have h_rec5 : a * x^5 + b * y^5 = P * (a * x^4 + b * y^4) - Q * (a * x^3 + b * y^3) := by
    calc
      a * x^5 + b * y^5 = a * x^3 * x^2 + b * y^3 * y^2 := by ring
      _ = a * x^3 * (P * x - Q) + b * y^3 * (P * y - Q) := by
        rw [show x^2 = P * x - Q by ring]
        rw [show y^2 = P * y - Q by ring]
      _ = P * (a * x^4 + b * y^4) - Q * (a * x^3 + b * y^3) := by ring

  have h_S5_val : a * x^5 + b * y^5 = 20 := by
    rw [h_rec5]
    rw [h₃, h₂]
    rw [h_P, h_Q]
    norm_num

  exact h_S5_val
