import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1
  (x : ℝ)
  (h₀ : abs (x - 1) + abs x + abs (x + 1) = x + 2) :
  0 ≤ x ∧ x ≤ 1 := by
  by_cases h₁ : x ≥ 1
  · -- Case x ≥ 1
    have h₂ : abs (x - 1) = x - 1 := by
      rw [abs_of_nonneg]
      linarith
    have h₃ : abs x = x := by
      rw [abs_of_nonneg]
      linarith
    have h₄ : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg]
      linarith
    rw [h₂, h₃, h₄] at h₀
    have h₅ : 3 * x = x + 2 := by linarith
    have h₆ : x = 1 := by linarith
    exact ⟨by linarith, by linarith⟩
  · -- Case x < 1
    by_cases h₂ : x ≥ 0
    · -- Subcase 0 ≤ x < 1
      have h₃ : x - 1 < 0 := by
        have h₃' : x < 1 := lt_of_not_ge h₁
        linarith
      have h₄ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg h₃]
      have h₅ : abs x = x := by
        rw [abs_of_nonneg]
        linarith
      have h₆ : abs (x + 1) = x + 1 := by
        rw [abs_of_nonneg]
        linarith
      rw [h₄, h₅, h₆] at h₀
      have h₇ : -(x - 1) + x + (x + 1) = x + 2 := by linarith
      have h₈ : x + 2 = x + 2 := by linarith
      exact ⟨by linarith, by linarith⟩
    · -- Subcase x < 0
      have h₃ : x < 0 := lt_of_not_ge h₂
      have h₄ : abs x = -x := by
        rw [abs_of_neg h₃]
      have h₅ : x - 1 < 0 := by linarith [h₃]
      have h₆ : abs (x - 1) = -(x - 1) := by
        rw [abs_of_neg h₅]
      by_cases h₇ : x + 1 ≥ 0
      · -- Sub-subcase -1 ≤ x < 0
        have h₈ : abs (x + 1) = x + 1 := by
          rw [abs_of_nonneg h₇]
        rw [h₆, h₄, h₈] at h₀
        have h₉ : -(x - 1) + (-x) + (x + 1) = x + 2 := by linarith
        have h₁₀ : 2 - x = x + 2 := by linarith
        have h₁₁ : x = 0 := by linarith
        linarith
      · -- Sub-subcase x < -1
        have h₈ : x + 1 < 0 := by
          have h₈' : ¬x + 1 ≥ 0 := h₇
          have h₈'' : x + 1 < 0 := lt_of_not_ge h₈'
          exact h₈''
        have h₉ : abs (x + 1) = -(x + 1) := by
          rw [abs_of_neg h₈]
        rw [h₆, h₄, h₉] at h₀
        have h₁₀ : -(x - 1) + (-x) + (-(x + 1)) = x + 2 := by linarith
        have h₁₁ : -3 * x = x + 2 := by linarith
        have h₁₂ : x = -1 / 2 := by linarith
        exfalso
        have h₁₃ : x < -1 := by
          have h₁₃' : x + 1 < 0 := h₈
          linarith
        linarith
