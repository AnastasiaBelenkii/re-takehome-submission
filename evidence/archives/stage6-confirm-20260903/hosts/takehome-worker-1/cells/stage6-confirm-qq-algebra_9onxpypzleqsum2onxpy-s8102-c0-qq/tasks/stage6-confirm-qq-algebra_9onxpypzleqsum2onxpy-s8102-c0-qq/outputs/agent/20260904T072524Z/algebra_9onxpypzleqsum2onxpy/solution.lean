import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_9onxpypzleqsum2onxpy
  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  have h₁ : 0 < x := h₀.1
  have h₂ : 0 < y := h₀.2.1
  have h₃ : 0 < z := h₀.2.2
  have h₄ : 0 < x + y := add_pos h₁ h₂
  have h₅ : 0 < y + z := add_pos h₂ h₃
  have h₆ : 0 < z + x := add_pos h₃ h₁
  have h₇ : 0 < x + y + z := add_pos (add_pos h₁ h₂) h₃
  
  -- Helper lemma: 1/a + 1/b ≥ 4/(a+b) for a,b > 0
  have h₈ : 1 / (x + y) + 1 / (y + z) ≥ 4 / (x + 2*y + z) := by
    have h₈₁ : 0 < x + y := h₄
    have h₈₂ : 0 < y + z := h₅
    have h₈₃ : 0 < x + 2*y + z := by positivity
    
    field_simp [h₈₁.ne', h₈₂.ne', h₈₃.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (x - z)]
  
  have h₉ : 1 / (y + z) + 1 / (z + x) ≥ 4 / (y + 2*z + x) := by
    have h₉₁ : 0 < y + z := h₅
    have h₉₂ : 0 < z + x := h₆
    have h₉₃ : 0 < y + 2*z + x := by positivity
    
    field_simp [h₉₁.ne', h₉₂.ne', h₉₃.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (y - x)]
  
  have h₁₀ : 1 / (z + x) + 1 / (x + y) ≥ 4 / (z + 2*x + y) := by
    have h₁₀₁ : 0 < z + x := h₆
    have h₁₀₂ : 0 < x + y := h₄
    have h₁₀₃ : 0 < z + 2*x + y := by positivity
    
    field_simp [h₁₀₁.ne', h₁₀₂.ne', h₁₀₃.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (z - y)]
  
  -- Step 2: Sum the three inequalities to get a bound on 2*(sum of reciprocals)
  have h₁₁ : 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 
    4 / (x + 2*y + z) + 4 / (y + 2*z + x) + 4 / (z + 2*x + y) := by
    linarith [h₈, h₉, h₁₀]
  
  -- Step 3: Apply Cauchy-Schwarz (Titu's lemma) to the RHS
  have h₁₂ : 4 / (x + 2*y + z) + 4 / (y + 2*z + x) + 4 / (z + 2*x + y) ≥ 9 / (x + y + z) := by
    have h₁₂₁ : 0 < x + 2*y + z := by positivity
    have h₁₂₂ : 0 < y + 2*z + x := by positivity
    have h₁₂₃ : 0 < z + 2*x + y := by positivity
    
    field_simp [h₁₂₁.ne', h₁₂₂.ne', h₁₂₃.ne', h₇.ne']
    rw [← sub_nonneg]
    ring_nf
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  
  -- Step 4: Combine everything to finish the proof
  calc
    9 / (x + y + z) ≤ 4 / (x + 2*y + z) + 4 / (y + 2*z + x) + 4 / (z + 2*x + y) := by
      exact h₁₂
    _ ≤ 2 * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
      linarith [h₁₁]
    _ = 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by ring
