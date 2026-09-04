import Mathlib

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  have h₁ : 0 ≤ x := by
    by_contra hx
    have hx_neg : x < 0 := by linarith
    
    by_cases h : x + 1 < 0
    · -- Case x < -1
      have h_abs_x_minus_1 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg hx_neg]
      have h_abs_x_plus_1 : abs (x + 1) = -(x + 1) := by
        rw [abs_of_neg h]
      
      have h_eq : -3 * x = x + 2 := by
        calc
          -3 * x = (1 - x) + (-x) + (-(x + 1)) := by ring
          _ = abs (x - 1) + abs x + abs (x + 1) := by rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
          _ = x + 2 := h₀
      
      have h_sol : x = -1 / 2 := by linarith
      have h_contra : x < -1 := by linarith
      linarith
    · -- Case x + 1 ≥ 0
      have h_abs_x_minus_1 : abs (x - 1) = 1 - x := by
        rw [abs_of_neg (by linarith)]
        ring
      have h_abs_x : abs x = -x := by
        rw [abs_of_neg hx_neg]
      have h_abs_x_plus_1 : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg (by linarith)]
      
      have h_eq : 2 - x = x + 2 := by
        calc
          2 - x = (1 - x) + (-x) + (x + 1) := by ring
          _ = abs (x - 1) + abs x + abs (x + 1) := by rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
          _ = x + 2 := h₀
      
      have h_sol : x = 0 := by linarith
      have h_contra : x < 0 := hx_neg
      linarith
  
  have h₂ : x ≤ 1 := by
    by_contra hx
    have hx_gt_1 : x > 1 := by linarith
    
    have h_abs_x_minus_1 : abs (x - 1) = x - 1 := by
      rw [abs_of_pos (by linarith)]
    have h_abs_x : abs x = x := by
      rw [abs_of_pos (by linarith)]
    have h_abs_x_plus_1 : abs (x + 1) = x + 1 := by
      rw [abs_of_pos (by linarith)]
    
    have h_eq : 3 * x = x + 2 := by
      calc
        3 * x = (x - 1) + x + (x + 1) := by ring
        _ = abs (x - 1) + abs x + abs (x + 1) := by rw [h_abs_x_minus_1, h_abs_x, h_abs_x_plus_1]
        _ = x + 2 := h₀
    
    have h_sol : x = 1 := by linarith
    have h_contra : x > 1 := hx_gt_1
    linarith
  
  exact ⟨h₁, h₂⟩
