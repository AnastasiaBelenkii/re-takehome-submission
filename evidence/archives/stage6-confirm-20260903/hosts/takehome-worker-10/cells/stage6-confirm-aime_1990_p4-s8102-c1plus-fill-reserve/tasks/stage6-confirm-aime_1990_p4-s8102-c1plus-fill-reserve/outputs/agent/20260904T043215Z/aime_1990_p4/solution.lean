import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p4
  (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x^2 - 10 * x - 29 ≠ 0)
  (h₂ : x^2 - 10 * x - 45 ≠ 0)
  (h₃ : x^2 - 10 * x - 69 ≠ 0)
  (h₄ : 1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0) :
  x = 13 := by
  set A := x^2 - 10 * x - 29 with hA_def
  set B := x^2 - 10 * x - 45 with hB_def
  set C := x^2 - 10 * x - 69 with hC_def
  
  have hA_ne : A ≠ 0 := by rw [hA_def]; exact h₁
  have hB_ne : B ≠ 0 := by rw [hB_def]; exact h₂
  have hC_ne : C ≠ 0 := by rw [hC_def]; exact h₃
  
  have hB_eq : B = A - 16 := by
    rw [hB_def, hA_def]
    ring
  
  have hC_eq : C = A - 40 := by
    rw [hC_def, hA_def]
    ring
  
  have hA_val : A = 10 := by
    have h_eq : 1 / A + 1 / B - 2 / C = 0 := by
      rw [hA_def, hB_def, hC_def] at h₄
      exact h₄
    
    rw [hB_eq, hC_eq] at h_eq
    have hB_ne_A : A - 16 ≠ 0 := by
      intro h
      apply hB_ne
      rw [hB_eq]
      exact h
    have hC_ne_A : A - 40 ≠ 0 := by
      intro h
      apply hC_ne
      rw [hC_eq]
      exact h
      
    field_simp [hA_ne, hB_ne_A, hC_ne_A] at h_eq
    ring_nf at h_eq
    linarith
  
  have h_x_quad : x^2 - 10 * x - 39 = 0 := by
    rw [hA_def] at hA_val
    linarith
  
  have h_x_factored : (x - 13) * (x + 3) = 0 := by
    calc
      (x - 13) * (x + 3) = x^2 - 10 * x - 39 := by ring
      _ = 0 := by rw [h_x_quad]
  
  have h_disj : x - 13 = 0 ∨ x + 3 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h_x_factored
  
  cases' h_disj with h h
  · rw [sub_eq_zero] at h
    exact h
  · exfalso
    linarith
