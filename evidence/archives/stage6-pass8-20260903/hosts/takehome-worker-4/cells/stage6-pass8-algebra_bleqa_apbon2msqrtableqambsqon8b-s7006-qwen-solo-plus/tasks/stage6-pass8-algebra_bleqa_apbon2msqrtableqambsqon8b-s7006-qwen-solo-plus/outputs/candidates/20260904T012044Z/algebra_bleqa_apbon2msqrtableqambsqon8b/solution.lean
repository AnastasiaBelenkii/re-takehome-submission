import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_bleqa_apbon2msqrtableqambsqon8b
  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  have h₂ : 0 < b := h₀.2
  have h₃ : 0 < a := h₀.1
  have h₄ : 0 < a * b := mul_pos h₃ h₂
  
  -- Identity 1
  have h₅ : (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b)^2 / 2 := by
    have h₆ : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (le_of_lt h₃)]
    calc
      (a + b) / 2 - Real.sqrt (a * b) = (a + b) / 2 - Real.sqrt a * Real.sqrt b := by rw [h₆]
      _ = (Real.sqrt a ^ 2 + Real.sqrt b ^ 2) / 2 - Real.sqrt a * Real.sqrt b := by
        rw [Real.sq_sqrt (le_of_lt h₃), Real.sq_sqrt (le_of_lt h₂)]
      _ = (Real.sqrt a ^ 2 - 2 * Real.sqrt a * Real.sqrt b + Real.sqrt b ^ 2) / 2 := by ring
      _ = (Real.sqrt a - Real.sqrt b)^2 / 2 := by ring

  -- Identity 2
  have h₇ : (a - b)^2 = (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 := by
    have h₈ : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
      have h₉ : Real.sqrt a ^ 2 = a := Real.sq_sqrt (le_of_lt h₃)
      have h₁₀ : Real.sqrt b ^ 2 = b := Real.sq_sqrt (le_of_lt h₂)
      calc
        a - b = Real.sqrt a ^ 2 - Real.sqrt b ^ 2 := by rw [h₉, h₁₀]
        _ = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by ring
    calc
      (a - b)^2 = ((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b))^2 := by rw [h₈]
      _ = (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 := by ring

  -- Main Inequality
  have h₈ : (Real.sqrt a - Real.sqrt b)^2 / 2 ≤ (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by
    by_cases h₉ : Real.sqrt a = Real.sqrt b
    · -- Case sqrt(a) = sqrt(b)
      have h₁₀ : a = b := by
        have h₁₁ : Real.sqrt a = Real.sqrt b := h₉
        have h₁₂ : Real.sqrt a ^ 2 = Real.sqrt b ^ 2 := by rw [h₁₁]
        have h₁₃ : a = b := by
          rw [Real.sq_sqrt (le_of_lt h₃), Real.sq_sqrt (le_of_lt h₂)] at h₁₂
          linarith
        exact h₁₃
      simp [h₁₀]
    · -- Case sqrt(a) ≠ sqrt(b)
      have h₁₀ : 0 < (Real.sqrt a - Real.sqrt b)^2 := by
        apply sq_pos_of_ne_zero
        intro h₁₁
        apply h₉
        linarith
      
      -- We need to show 1/2 ≤ (sqrt(a) + sqrt(b))^2 / (8 * b)
      have h₁₁ : 4 * b ≤ (Real.sqrt a + Real.sqrt b)^2 := by
        have h₁₂ : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
        have h₁₃ : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
        have h₁₄ : Real.sqrt a ≥ Real.sqrt b := by
          apply Real.sqrt_le_sqrt
          linarith
        nlinarith [sq_sqrt (le_of_lt h₃), sq_sqrt (le_of_lt h₂),
          mul_self_nonneg (Real.sqrt a - Real.sqrt b)]
      
      have h₁₂ : 0 < 8 * b := by positivity
      have h₁₃ : (1 : ℝ) / 2 ≤ (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by
        have h₁₄ : (1 : ℝ) / 2 = 4 * b / (8 * b) := by
          field_simp [h₁₂.ne']
          <;> ring_nf
          <;> linarith
        calc
          (1 : ℝ) / 2 = 4 * b / (8 * b) := by rw [h₁₄]
          _ ≤ (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by
            gcongr
            <;> linarith
      
      -- Multiply by (sqrt(a) - sqrt(b))^2
      have h₁₄ : (Real.sqrt a - Real.sqrt b)^2 / 2 ≤ (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by
        calc
          (Real.sqrt a - Real.sqrt b)^2 / 2 = (Real.sqrt a - Real.sqrt b)^2 * (2⁻¹ : ℝ) := by
            field_simp [show (2 : ℝ) ≠ 0 by norm_num]
            <;> ring
          _ ≤ (Real.sqrt a - Real.sqrt b)^2 * ((Real.sqrt a + Real.sqrt b)^2 / (8 * b)) := by
            gcongr
            <;> linarith
          _ = (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by ring
      
      exact h₁₄
  
  -- Combine
  calc
    (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b)^2 / 2 := by rw [h₅]
    _ ≤ (Real.sqrt a - Real.sqrt b)^2 * (Real.sqrt a + Real.sqrt b)^2 / (8 * b) := by
      exact h₈
    _ = (a - b)^2 / (8 * b) := by
      rw [h₇]
      <;> ring_nf
