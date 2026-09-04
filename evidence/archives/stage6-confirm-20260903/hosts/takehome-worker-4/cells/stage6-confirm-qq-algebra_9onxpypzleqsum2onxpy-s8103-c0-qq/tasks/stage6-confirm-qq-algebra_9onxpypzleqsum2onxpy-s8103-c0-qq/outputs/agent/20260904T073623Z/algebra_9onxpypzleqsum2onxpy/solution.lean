import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x + y := by linarith [h₀.1, h₀.2.1]
  have h₂ : 0 < y + z := by linarith [h₀.2.1, h₀.2.2]
  have h₃ : 0 < z + x := by linarith [h₀.2.2, h₀.1]
  have h₄ : 0 < x + y + z := by linarith [h₀.1, h₀.2.1, h₀.2.2]
  
  have h₅ : 0 < 2 * (x + y + z) := by positivity
  
  have h₆ : (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) * (2 * (x + y + z)) ≥ 18 := by
    have h₆₁ : 0 < x + y := by linarith
    have h₆₂ : 0 < y + z := by linarith
    have h₆₃ : 0 < z + x := by linarith
    
    field_simp [h₆₁.ne', h₆₂.ne', h₆₃.ne']
    rw [mul_comm]
    apply le_of_sub_nonneg
    field_simp [h₆₁.ne', h₆₂.ne', h₆₃.ne']
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  have h₇ : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 9 / (x + y + z) := by
    have h₇₁ : 0 < 2 * (x + y + z) := by positivity
    have h₇₂ : (2 / (x + y) + 2 / (y + z) + 2 / (z + x)) * (2 * (x + y + z)) ≥ 18 := h₆
    have h₇₃ : 2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 18 / (2 * (x + y + z)) := by
      calc
        2 / (x + y) + 2 / (y + z) + 2 / (z + x) 
          = ((2 / (x + y) + 2 / (y + z) + 2 / (z + x)) * (2 * (x + y + z))) / (2 * (x + y + z)) := by
            field_simp [h₇₁.ne']
            <;> ring
        _ ≥ 18 / (2 * (x + y + z)) := by
          gcongr
          <;> assumption
    calc
      2 / (x + y) + 2 / (y + z) + 2 / (z + x) ≥ 18 / (2 * (x + y + z)) := h₇₃
      _ = 9 / (x + y + z) := by
        field_simp [h₄.ne']
        <;> ring
  
  exact h₇
