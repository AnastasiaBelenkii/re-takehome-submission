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
    have h₄₂ : b > 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b)]
    have h₄₃ : c > 0 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (a - b)]
    have h₄₄ : a * b + b * c + c * a < 0 := by
      nlinarith [mul_pos h₄₂ h₄₃]
    linarith
  
  have h₅ : a ≤ 1 / 3 := by
    by_contra h
    have h₅₁ : a > 1 / 3 := by linarith
    have h₅₂ : b ≥ 1 / 3 := by linarith [h₀.1]
    have h₅₃ : c ≥ 1 / 3 := by linarith [h₀.2]
    have h₅₄ : a * b + b * c + c * a > 1 := by
      have h₅₄₁ : a ≥ 1 / 3 := by linarith
      have h₅₄₂ : b ≥ 1 / 3 := by linarith
      have h₅₄₃ : c ≥ 1 / 3 := by linarith
      nlinarith [mul_nonneg (sub_nonneg.mpr h₅₄₁) (sub_nonneg.mpr h₅₄₂),
                 mul_nonneg (sub_nonneg.mpr h₅₄₂) (sub_nonneg.mpr h₅₄₃),
                 mul_nonneg (sub_nonneg.mpr h₅₄₃) (sub_nonneg.mpr h₅₄₁)]
    linarith
  
  have h₆ : 1 / 3 ≤ b := by
    by_contra h
    have h₆₁ : b < 1 / 3 := by linarith
    have h₆₂ : a ≤ 1 / 3 := by linarith [h₅]
    have h₆₃ : c ≥ 1 := by
      have h₆₄ : a + b + c = 2 := h₁
      have h₆₅ : a ≤ b := h₀.1
      have h₆₆ : b < 1 / 3 := h₆₁
      have h₆₇ : a < 1 / 3 := by linarith
      nlinarith
    have h₆₈ : a * b + b * c + c * a < 1 := by
      have h₆₉ : a * b < 1 / 9 := by
        nlinarith
      have h₆₁₀ : b * c < 1 / 3 := by
        nlinarith
      have h₆₁₁ : c * a ≤ 1 / 3 := by
        nlinarith
      nlinarith
    linarith
  
  have h₇ : b ≤ 1 := by
    by_contra h
    have h₇₁ : b > 1 := by linarith
    have h₇₂ : c ≥ 1 := by linarith [h₀.2]
    have h₇₃ : a ≤ 1 / 3 := by linarith [h₅]
    have h₇₄ : a * b + b * c + c * a > 1 := by
      have h₇₅ : a * b > a := by
        nlinarith
      have h₇₆ : b * c > 1 := by
        nlinarith
      have h₇₇ : c * a ≥ 0 := by
        nlinarith
      nlinarith
    linarith
  
  have h₈ : 1 ≤ c := by
    by_contra h
    have h₈₁ : c < 1 := by linarith
    have h₈₂ : b ≤ 1 := by linarith [h₇]
    have h₈₃ : a ≤ 1 / 3 := by linarith [h₅]
    have h₈₄ : a * b + b * c + c * a < 1 := by
      have h₈₅ : a * b ≤ 1 / 3 := by
        nlinarith
      have h₈₆ : b * c < 1 := by
        nlinarith
      have h₈₇ : c * a < 1 / 3 := by
        nlinarith
      nlinarith
    linarith
  
  have h₉ : c ≤ 4 / 3 := by
    by_contra h
    have h₉₁ : c > 4 / 3 := by linarith
    have h₉₂ : a ≤ 1 / 3 := by linarith [h₅]
    have h₉₃ : b ≤ 1 := by linarith [h₇]
    have h₉₄ : a * b + b * c + c * a > 1 := by
      have h₉₅ : b * c > 4 / 3 := by
        nlinarith
      have h₉₆ : c * a ≥ 0 := by
        nlinarith
      have h₉₇ : a * b ≥ 0 := by
        nlinarith
      nlinarith
    linarith
  
  exact ⟨h₄, h₅, h₆, h₇, h₈, h₉⟩
