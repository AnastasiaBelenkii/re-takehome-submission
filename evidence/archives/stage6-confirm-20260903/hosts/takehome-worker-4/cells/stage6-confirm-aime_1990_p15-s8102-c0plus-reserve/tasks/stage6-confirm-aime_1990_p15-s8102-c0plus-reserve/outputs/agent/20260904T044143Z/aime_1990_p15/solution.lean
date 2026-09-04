import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1990_p15
  (a b x y : ℝ)
  (h₀ : a * x + b * y = 3)
  (h₁ : a * x^2 + b * y^2 = 7)
  (h₂ : a * x^3 + b * y^3 = 16)
  (h₃ : a * x^4 + b * y^4 = 42) :
  a * x^5 + b * y^5 = 20 := by
  -- Define s = x + y and p = x * y
  set s := x + y
  set p := x * y
  
  -- Key lemma: x^n = s*x^(n-1) - p*x^(n-2) for n ≥ 2
  have hx_pow : ∀ n : ℕ, n ≥ 2 → x^n = s * x^(n-1) - p * x^(n-2) := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 2
      calc
        x^2 = x^2 := rfl
        _ = (x + y) * x - (x * y) * 1 := by ring
        _ = s * x - p * x^0 := by simp [s, p]
        _ = s * x^(2-1) - p * x^(2-2) := by norm_num
    · -- Inductive step
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => 
          -- n = 2 case already handled
          simp_all [pow_succ]
          <;> ring_nf at *
          <;> linarith
        | succ n =>
          simp_all [pow_succ]
          <;> ring_nf at *
          <;> nlinarith
  
  -- Key lemma: y^n = s*y^(n-1) - p*y^(n-2) for n ≥ 2
  have hy_pow : ∀ n : ℕ, n ≥ 2 → y^n = s * y^(n-1) - p * y^(n-2) := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 2
      calc
        y^2 = y^2 := rfl
        _ = (x + y) * y - (x * y) * 1 := by ring
        _ = s * y - p * y^0 := by simp [s, p]
        _ = s * y^(2-1) - p * y^(2-2) := by norm_num
    · -- Inductive step
      cases n with
      | zero => contradiction
      | succ n =>
        cases n with
        | zero => 
          -- n = 2 case already handled
          simp_all [pow_succ]
          <;> ring_nf at *
          <;> linarith
        | succ n =>
          simp_all [pow_succ]
          <;> ring_nf at *
          <;> nlinarith
  
  -- Lemma: S_n = s*S_{n-1} - p*S_{n-2} for n ≥ 2
  have h_recurrence : ∀ n : ℕ, n ≥ 2 → a * x^n + b * y^n = s * (a * x^(n-1) + b * y^(n-1)) - p * (a * x^(n-2) + b * y^(n-2)) := by
    intro n hn
    have hx := hx_pow n hn
    have hy := hy_pow n hn
    calc
      a * x^n + b * y^n = a * (s * x^(n-1) - p * x^(n-2)) + b * (s * y^(n-1) - p * y^(n-2)) := by rw [hx, hy]
      _ = s * (a * x^(n-1) + b * y^(n-1)) - p * (a * x^(n-2) + b * y^(n-2)) := by ring
  
  -- Use the recurrence to find s and p
  have h_s_eq : s = -14 := by
    have h3 := h_recurrence 3 (by norm_num)
    have h4 := h_recurrence 4 (by norm_num)
    simp [h₀, h₁, h₂, h₃, s, p] at h3 h4
    -- From h3: 16 = s*7 - p*3
    -- From h4: 42 = s*16 - p*7
    -- Solve this system
    have h5 : 7 * s - 3 * p = 16 := by linarith
    have h6 : 16 * s - 7 * p = 42 := by linarith
    -- Multiply first by 7: 49*s - 21*p = 112
    -- Multiply second by 3: 48*s - 21*p = 126
    -- Subtract: s = -14
    nlinarith
  
  have h_p_eq : p = -38 := by
    have h3 := h_recurrence 3 (by norm_num)
    simp [h₀, h₁, h₂, h₃, s, p] at h3
    have h5 : 7 * s - 3 * p = 16 := by linarith
    rw [h_s_eq] at h5
    linarith
  
  -- Calculate S_5
  have h_main : a * x^5 + b * y^5 = 20 := by
    have h5 := h_recurrence 5 (by norm_num)
    simp [h₀, h₁, h₂, h₃, s, p, h_s_eq, h_p_eq] at h5 ⊢
    <;> linarith
  
  exact h_main
