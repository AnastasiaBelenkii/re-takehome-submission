import Mathlib

set_option maxHeartbeats 0

theorem algebra_amgm_sumasqdivbgeqsuma
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  
  have h₁ : a ^ 2 / b + b ≥ 2 * a := by
    field_simp [hb.ne']
    rw [← sub_nonneg]
    have : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
    nlinarith
  
  have h₂ : b ^ 2 / c + c ≥ 2 * b := by
    field_simp [hc.ne']
    rw [← sub_nonneg]
    have : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
    nlinarith
  
  have h₃ : c ^ 2 / d + d ≥ 2 * c := by
    field_simp [hd.ne']
    rw [← sub_nonneg]
    have : 0 ≤ (c - d) ^ 2 := sq_nonneg (c - d)
    nlinarith
  
  have h₄ : d ^ 2 / a + a ≥ 2 * d := by
    field_simp [ha.ne']
    rw [← sub_nonneg]
    have : 0 ≤ (d - a) ^ 2 := sq_nonneg (d - a)
    nlinarith
  
  have h_sum : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d) ≥ 2 * (a + b + c + d) := by
    calc
      a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a + (a + b + c + d)
        = (a ^ 2 / b + b) + (b ^ 2 / c + c) + (c ^ 2 / d + d) + (d ^ 2 / a + a) := by ring
      _ ≥ 2 * a + 2 * b + 2 * c + 2 * d := by
        linarith [h₁, h₂, h₃, h₄]
      _ = 2 * (a + b + c + d) := by ring
  
  have h_final : a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := by
    linarith [h_sum]
  
  exact h_final
