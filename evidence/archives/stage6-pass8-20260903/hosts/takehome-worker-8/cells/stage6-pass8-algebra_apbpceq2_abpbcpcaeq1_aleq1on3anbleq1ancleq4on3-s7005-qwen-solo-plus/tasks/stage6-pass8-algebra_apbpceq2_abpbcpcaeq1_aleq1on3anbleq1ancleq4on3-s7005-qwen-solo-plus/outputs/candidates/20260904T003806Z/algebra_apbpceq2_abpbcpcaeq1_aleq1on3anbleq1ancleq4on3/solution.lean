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
    -- Use contradiction: if a < 0, then from a ≤ b ≤ c and a + b + c = 2,
    -- we'd get contradictions with ab + bc + ca = 1
    by_contra h
    have h₄ : a < 0 := by linarith
    have h₅ : b ≥ a := h₀.1
    have h₆ : c ≥ b := h₀.2
    have h₇ : a + b + c = 2 := h₁
    have h₈ : a * b + b * c + c * a = 1 := h₂
    -- If a < 0 and b ≥ a, c ≥ b, then ab + bc + ca would be problematic
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c)]
  
  have h₄ : a ≤ 1 / 3 := by
    -- Use the fact that (a-b)² + (b-c)² + (c-a)² ≥ 0 and the given constraints
    have h₅ : (a - b)^2 + (b - c)^2 + (c - a)^2 ≥ 0 := by positivity
    have h₆ : a + b + c = 2 := h₁
    have h₇ : a * b + b * c + c * a = 1 := h₂
    have h₈ : a ≤ b := h₀.1
    have h₉ : b ≤ c := h₀.2
    -- Expand and use the constraints to bound a
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3)]
  
  have h₅ : 1 / 3 ≤ b := by
    -- Similar approach: use the constraints to bound b from below
    have h₆ : a + b + c = 2 := h₁
    have h₇ : a * b + b * c + c * a = 1 := h₂
    have h₈ : a ≤ b := h₀.1
    have h₉ : b ≤ c := h₀.2
    -- Use the relationship between the variables
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 1/3)]
  
  have h₆ : b ≤ 1 := by
    -- Bound b from above using the constraints
    have h₇ : a + b + c = 2 := h₁
    have h₈ : a * b + b * c + c * a = 1 := h₂
    have h₉ : a ≤ b := h₀.1
    have h₁₀ : b ≤ c := h₀.2
    -- Use the ordering and sum constraints
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have h₇ : 1 ≤ c := by
    -- Bound c from below
    have h₈ : a + b + c = 2 := h₁
    have h₉ : a * b + b * c + c * a = 1 := h₂
    have h₁₀ : a ≤ b := h₀.1
    have h₁₁ : b ≤ c := h₀.2
    -- Use the constraints to show c ≥ 1
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  
  have h₈ : c ≤ 4 / 3 := by
    -- Bound c from above
    have h₉ : a + b + c = 2 := h₁
    have h₁₀ : a * b + b * c + c * a = 1 := h₂
    have h₁₁ : a ≤ b := h₀.1
    have h₁₂ : b ≤ c := h₀.2
    -- Use the constraints to show c ≤ 4/3
    nlinarith [sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg (c - 4/3)]
  
  exact ⟨h₃, h₄, h₅, h₆, h₇, h₈⟩
