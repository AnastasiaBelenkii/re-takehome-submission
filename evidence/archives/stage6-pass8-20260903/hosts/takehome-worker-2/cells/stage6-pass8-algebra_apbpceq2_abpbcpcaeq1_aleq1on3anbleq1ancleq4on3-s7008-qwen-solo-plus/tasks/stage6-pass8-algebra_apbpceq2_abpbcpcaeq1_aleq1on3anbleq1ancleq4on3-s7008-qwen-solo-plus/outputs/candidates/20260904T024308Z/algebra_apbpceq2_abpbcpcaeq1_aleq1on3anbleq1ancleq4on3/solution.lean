import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : 0 ≤ a := by
    -- Use contradiction: if a < 0, then ab + bc + ca would be too small
    by_contra h
    have h₄ : a < 0 := by linarith
    have h₅ : b ≥ a := h₀.1
    have h₆ : c ≥ b := h₀.2
    have h₇ : c ≥ a := by linarith
    -- Since a < 0 and b, c ≥ a, we need to show ab + bc + ca < 1
    have h₈ : a + b + c = 2 := h₁
    have h₉ : a * b + b * c + c * a = 1 := h₂
    -- Using the fact that a < 0 and b, c are bounded below by a
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]
  
  have h₄ : a ≤ 1 / 3 := by
    -- Use the constraint that a ≤ b ≤ c and the sum/product relations
    have h₅ : a ≤ b := h₀.1
    have h₆ : b ≤ c := h₀.2
    have h₇ : a + b + c = 2 := h₁
    have h₈ : a * b + b * c + c * a = 1 := h₂
    -- Consider the quadratic in terms of b and c
    nlinarith [sq_nonneg (b - c), sq_nonneg (a - 1/3), 
      mul_nonneg (sub_nonneg.mpr h₅) (sub_nonneg.mpr h₆)]
  
  have h₅ : 1 / 3 ≤ b := by
    -- Use the ordering and sum constraints
    have h₆ : a ≤ b := h₀.1
    have h₇ : b ≤ c := h₀.2
    have h₈ : a + b + c = 2 := h₁
    have h₉ : a * b + b * c + c * a = 1 := h₂
    -- Show that b cannot be less than 1/3
    nlinarith [sq_nonneg (b - 1/3), sq_nonneg (a - b), sq_nonneg (b - c)]
  
  have h₆ : b ≤ 1 := by
    -- Use the ordering and sum constraints
    have h₇ : a ≤ b := h₀.1
    have h₈ : b ≤ c := h₀.2
    have h₉ : a + b + c = 2 := h₁
    have h₁₀ : a * b + b * c + c * a = 1 := h₂
    -- Show that b cannot exceed 1
    nlinarith [sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (b - c)]
  
  have h₇ : 1 ≤ c := by
    -- Use the ordering and sum constraints
    have h₈ : a ≤ b := h₀.1
    have h₉ : b ≤ c := h₀.2
    have h₁₀ : a + b + c = 2 := h₁
    have h₁₁ : a * b + b * c + c * a = 1 := h₂
    -- Show that c cannot be less than 1
    nlinarith [sq_nonneg (c - 1), sq_nonneg (a - b), sq_nonneg (b - c)]
  
  have h₈ : c ≤ 4 / 3 := by
    -- Use the ordering and sum constraints
    have h₉ : a ≤ b := h₀.1
    have h₁₀ : b ≤ c := h₀.2
    have h₁₁ : a + b + c = 2 := h₁
    have h₁₂ : a * b + b * c + c * a = 1 := h₂
    -- Show that c cannot exceed 4/3
    nlinarith [sq_nonneg (c - 4/3), sq_nonneg (a - b), sq_nonneg (b - c)]
  
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩
