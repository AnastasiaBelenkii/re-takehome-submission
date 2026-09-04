import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 := by
  have h₂ : 0 ≤ a := by linarith [h₀.1]
  have h₃ : 0 ≤ b := by linarith [h₀.2]
  
  -- Use convexity of x^n for n ≥ 1
  have h₄ : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
    apply convexOn_pow
    <;> norm_num
    <;> linarith
  
  have h₅ : a ∈ Set.Ici 0 := by exact Set.mem_Ici.mpr h₂
  have h₆ : b ∈ Set.Ici 0 := by exact Set.mem_Ici.mpr h₃
  
  -- Apply Jensen's inequality for convex functions
  have h₇ : (fun x : ℝ => x ^ n) ((1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b) ≤ 
            (1 / 2 : ℝ) • (fun x : ℝ => x ^ n) a + (1 / 2 : ℝ) • (fun x : ℝ => x ^ n) b := by
    apply h₄.2
    <;> simp_all [Set.mem_Ici]
    <;> norm_num
    <;> linarith
  
  -- Simplify the expressions
  have h₈ : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b = (a + b) / 2 := by
    field_simp [mul_comm]
    <;> ring
  
  have h₉ : (1 / 2 : ℝ) • (fun x : ℝ => x ^ n) a + (1 / 2 : ℝ) • (fun x : ℝ => x ^ n) b = (a ^ n + b ^ n) / 2 := by
    simp [smul_eq_mul]
    <;> ring
  
  rw [h₈] at h₇
  rw [h₉] at h₇
  simpa using h₇
