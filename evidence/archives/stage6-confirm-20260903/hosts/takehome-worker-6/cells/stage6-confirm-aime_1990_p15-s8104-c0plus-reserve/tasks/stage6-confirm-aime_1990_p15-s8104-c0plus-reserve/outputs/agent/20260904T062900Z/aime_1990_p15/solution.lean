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
  set p := x + y
  set q := x * y
  
  have h_rec1 : a * x^3 + b * y^3 = p * (a * x^2 + b * y^2) - q * (a * x + b * y) := by
    calc
      a * x^3 + b * y^3 = a * ((x + y) * x^2 - x * y * x) + b * ((x + y) * y^2 - x * y * y) := by
        have hx : x^3 = (x + y) * x^2 - x * y * x := by ring
        have hy : y^3 = (x + y) * y^2 - x * y * y := by ring
        rw [hx, hy]
      _ = (x + y) * (a * x^2 + b * y^2) - x * y * (a * x + b * y) := by ring
      _ = p * (a * x^2 + b * y^2) - q * (a * x + b * y) := by simp [p, q]
  
  have h_rec2 : a * x^4 + b * y^4 = p * (a * x^3 + b * y^3) - q * (a * x^2 + b * y^2) := by
    calc
      a * x^4 + b * y^4 = a * ((x + y) * x^3 - x * y * x^2) + b * ((x + y) * y^3 - x * y * y^2) := by
        have hx : x^4 = (x + y) * x^3 - x * y * x^2 := by ring
        have hy : y^4 = (x + y) * y^3 - x * y * y^2 := by ring
        rw [hx, hy]
      _ = (x + y) * (a * x^3 + b * y^3) - x * y * (a * x^2 + b * y^2) := by ring
      _ = p * (a * x^3 + b * y^3) - q * (a * x^2 + b * y^2) := by simp [p, q]
  
  have h_eq1 : p * 7 - q * 3 = 16 := by
    have h_temp : 16 = p * 7 - q * 3 := by
      calc
        16 = a * x^3 + b * y^3 := by rw [h₂]
        _ = p * (a * x^2 + b * y^2) - q * (a * x + b * y) := by rw [h_rec1]
        _ = p * 7 - q * 3 := by rw [h₁, h₀]
    linarith
  
  have h_eq2 : p * 16 - q * 7 = 42 := by
    have h_temp : 42 = p * 16 - q * 7 := by
      calc
        42 = a * x^4 + b * y^4 := by rw [h₃]
        _ = p * (a * x^3 + b * y^3) - q * (a * x^2 + b * y^2) := by rw [h_rec2]
        _ = p * 16 - q * 7 := by rw [h₂, h₁]
    linarith
  
  have h_p : p = -14 := by
    linarith [h_eq1, h_eq2]
    
  have h_q : q = -38 := by
    linarith [h_eq1, h_p]
  
  have h_rec3 : a * x^5 + b * y^5 = p * (a * x^4 + b * y^4) - q * (a * x^3 + b * y^3) := by
    calc
      a * x^5 + b * y^5 = a * ((x + y) * x^4 - x * y * x^3) + b * ((x + y) * y^4 - x * y * y^3) := by
        have hx : x^5 = (x + y) * x^4 - x * y * x^3 := by ring
        have hy : y^5 = (x + y) * y^4 - x * y * y^3 := by ring
        rw [hx, hy]
      _ = (x + y) * (a * x^4 + b * y^4) - x * y * (a * x^3 + b * y^3) := by ring
      _ = p * (a * x^4 + b * y^4) - q * (a * x^3 + b * y^3) := by simp [p, q]
  
  have h_S5 : a * x^5 + b * y^5 = 20 := by
    calc
      a * x^5 + b * y^5 = p * (a * x^4 + b * y^4) - q * (a * x^3 + b * y^3) := by rw [h_rec3]
      _ = (-14) * 42 - (-38) * 16 := by rw [h_p, h_q, h₃, h₂]
      _ = 20 := by norm_num
  
  exact h_S5
