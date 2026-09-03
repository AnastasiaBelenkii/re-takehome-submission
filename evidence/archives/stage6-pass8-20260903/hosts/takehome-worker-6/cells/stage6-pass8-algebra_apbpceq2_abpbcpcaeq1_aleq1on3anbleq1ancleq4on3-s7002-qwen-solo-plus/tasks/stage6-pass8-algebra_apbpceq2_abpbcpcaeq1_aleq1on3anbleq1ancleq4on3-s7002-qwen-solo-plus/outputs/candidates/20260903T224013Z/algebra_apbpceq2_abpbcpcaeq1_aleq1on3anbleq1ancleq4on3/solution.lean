import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
  (a b c : ℝ)
  (h₀ : a ≤ b ∧ b ≤ c)
  (h₁ : a + b + c = 2)
  (h₂ : a * b + b * c + c * a = 1) :
  0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := by
  have h₃ : a^2 + b^2 + c^2 = 2 := by
    have h₃₁ : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h₁] at h₃₁
    rw [h₂] at h₃₁
    linarith
  
  have h₄ : 0 ≤ a := by
    by_contra h
    have h₄₁ : a < 0 := by linarith
    have h₄₂ : a^2 > 0 := by nlinarith
    have h₄₃ : b ≥ a := h₀.1
    have h₄₄ : c ≥ b := h₀.2
    have h₄₅ : c ≥ a := by linarith
    have h₄₆ : a * b ≥ a^2 := by nlinarith
    have h₄₇ : b * c ≥ b^2 := by nlinarith
    have h₄₈ : c * a ≥ a^2 := by nlinarith
    nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h₅ : a ≤ 1 / 3 := by
    by_contra h
    have h₅₁ : a > 1 / 3 := by linarith
    have h₅₂ : b ≥ a := h₀.1
    have h₅₃ : c ≥ b := h₀.2
    have h₅₄ : a + b + c > 1 := by nlinarith
    have h₅₅ : a * b + b * c + c * a > 1 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    linarith
  
  have h₆ : 1 / 3 ≤ b := by
    by_contra h
    have h₆₁ : b < 1 / 3 := by linarith
    have h₆₂ : a ≤ b := h₀.1
    have h₆₃ : c ≥ b := h₀.2
    have h₆₄ : a + b + c < 2 := by nlinarith
    linarith
  
  have h₇ : b ≤ 1 := by
    by_contra h
    have h₇₁ : b > 1 := by linarith
    have h₇₂ : c ≥ b := h₀.2
    have h₇₃ : a ≤ b := h₀.1
    have h₇₄ : a + b + c > 2 := by nlinarith
    linarith
  
  have h₈ : 1 ≤ c := by
    by_contra h
    have h₈₁ : c < 1 := by linarith
    have h₈₂ : b ≤ c := h₀.2
    have h₈₃ : a ≤ b := h₀.1
    have h₈₄ : a + b + c < 2 := by nlinarith
    linarith
  
  have h₉ : c ≤ 4 / 3 := by
    by_contra h
    have h₉₁ : c > 4 / 3 := by linarith
    have h₉₂ : b ≤ c := h₀.2
    have h₉₃ : a ≤ b := h₀.1
    have h₉₄ : a + b + c > 2 := by nlinarith
    linarith
  
  exact ⟨h₄, h₅, h₆, h₇, h₈, h₉⟩
