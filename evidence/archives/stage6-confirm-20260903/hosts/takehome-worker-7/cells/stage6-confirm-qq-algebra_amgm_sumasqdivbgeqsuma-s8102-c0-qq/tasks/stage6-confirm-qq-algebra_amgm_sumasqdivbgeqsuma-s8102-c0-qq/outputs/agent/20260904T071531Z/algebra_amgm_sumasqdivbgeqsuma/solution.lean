import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  have h₁ : 0 < a := h₀.1
  have h₂ : 0 < b := h₀.2.1
  have h₃ : 0 < c := h₀.2.2.1
  have h₄ : 0 < d := h₀.2.2.2
  
  -- Use AM-GM: x²/y + y ≥ 2x for positive x, y
  have h₅ : a^2 / b + b ≥ 2 * a := by
    have h₅₁ : 0 < b := h₂
    have h₅₂ : 0 < a := h₁
    have h₅₃ : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
    have h₅₄ : a^2 + b^2 ≥ 2 * a * b := by
      nlinarith [sq_nonneg (a - b)]
    calc
      a^2 / b + b = (a^2 + b^2) / b := by field_simp [h₅₁.ne'] <;> ring
      _ ≥ (2 * a * b) / b := by gcongr <;> field_simp [h₅₁.ne'] <;> linarith
      _ = 2 * a := by field_simp [h₅₁.ne'] <;> ring
  
  have h₆ : b^2 / c + c ≥ 2 * b := by
    have h₆₁ : 0 < c := h₃
    have h₆₂ : 0 < b := h₂
    have h₆₃ : (b - c)^2 ≥ 0 := sq_nonneg (b - c)
    have h₆₄ : b^2 + c^2 ≥ 2 * b * c := by
      nlinarith [sq_nonneg (b - c)]
    calc
      b^2 / c + c = (b^2 + c^2) / c := by field_simp [h₆₁.ne'] <;> ring
      _ ≥ (2 * b * c) / c := by gcongr <;> field_simp [h₆₁.ne'] <;> linarith
      _ = 2 * b := by field_simp [h₆₁.ne'] <;> ring
  
  have h₇ : c^2 / d + d ≥ 2 * c := by
    have h₇₁ : 0 < d := h₄
    have h₇₂ : 0 < c := h₃
    have h₇₃ : (c - d)^2 ≥ 0 := sq_nonneg (c - d)
    have h₇₄ : c^2 + d^2 ≥ 2 * c * d := by
      nlinarith [sq_nonneg (c - d)]
    calc
      c^2 / d + d = (c^2 + d^2) / d := by field_simp [h₇₁.ne'] <;> ring
      _ ≥ (2 * c * d) / d := by gcongr <;> field_simp [h₇₁.ne'] <;> linarith
      _ = 2 * c := by field_simp [h₇₁.ne'] <;> ring
  
  have h₈ : d^2 / a + a ≥ 2 * d := by
    have h₈₁ : 0 < a := h₁
    have h₈₂ : 0 < d := h₄
    have h₈₃ : (d - a)^2 ≥ 0 := sq_nonneg (d - a)
    have h₈₄ : d^2 + a^2 ≥ 2 * d * a := by
      nlinarith [sq_nonneg (d - a)]
    calc
      d^2 / a + a = (d^2 + a^2) / a := by field_simp [h₈₁.ne'] <;> ring
      _ ≥ (2 * d * a) / a := by gcongr <;> field_simp [h₈₁.ne'] <;> linarith
      _ = 2 * d := by field_simp [h₈₁.ne'] <;> ring
  
  have h₉ : (a^2 / b + b) + (b^2 / c + c) + (c^2 / d + d) + (d^2 / a + a) ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
    linarith [h₅, h₆, h₇, h₈]
  
  have h₁₀ : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    ring_nf at h₉ ⊢
    linarith
  
  linarith
