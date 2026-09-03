import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h₂ : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
    apply convexOn_pow
    <;> norm_num
  
  have h₃ : a ∈ Set.Ici 0 := by
    exact Set.mem_Ici.mpr (le_of_lt h₀.1)
  
  have h₄ : b ∈ Set.Ici 0 := by
    exact Set.mem_Ici.mpr (le_of_lt h₀.2)
  
  have h₅ : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h₆ : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have h₇ : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  
  have h₈ : (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) ≤ (1 / 2 : ℝ) * (a ^ n) + (1 / 2 : ℝ) * (b ^ n) := by
    have h₈₁ : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := h₂
    have h₈₂ : a ∈ Set.Ici 0 := h₃
    have h₈₃ : b ∈ Set.Ici 0 := h₄
    have h₈₄ : 0 ≤ (1 / 2 : ℝ) := h₅
    have h₈₅ : 0 ≤ (1 / 2 : ℝ) := h₆
    have h₈₆ : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := h₇
    exact h₈₁.2 h₈₂ h₈₃ h₈₄ h₈₅ h₈₆
  
  have h₉ : (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 := by ring
  
  have h₁₀ : (1 / 2 : ℝ) * (a ^ n) + (1 / 2 : ℝ) * (b ^ n) = (a ^ n + b ^ n) / 2 := by ring
  
  calc
    ((a + b) / 2)^n = (fun x : ℝ => x ^ n) ((a + b) / 2) := by simp
    _ = (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b) := by rw [h₉]
    _ ≤ (1 / 2 : ℝ) * (a ^ n) + (1 / 2 : ℝ) * (b ^ n) := h₈
    _ = (a ^ n + b ^ n) / 2 := by rw [h₁₀]
