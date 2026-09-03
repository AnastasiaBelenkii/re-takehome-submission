import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First show that 6 ∈ S, i.e., 6! < 3^6
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by norm_num [Nat.factorial]
  
  -- Then show that for all n ≥ 7, n! ≥ 3^n (so n ∉ S)
  have h_inductive : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 7
      norm_num [Nat.factorial]
    · -- Inductive step: assume true for k, prove for k+1
      simp_all [Nat.factorial, pow_succ]
      have h₁ : 0 < 3 := by norm_num
      have h₂ : 0 < k + 1 := by omega
      have h₃ : 0 < 3 ^ k := pow_pos (by norm_num : (0 : ℕ) < 3) k
      nlinarith
  
  -- Show that for any n in S, n ≤ 6
  have h_upper_bound : ∀ n : ℕ, n ∈ {n : ℕ | Nat.factorial n < 3 ^ n} → n ≤ 6 := by
    intro n hn
    by_contra h
    -- If n > 6, then n ∉ S
    have h_gt : n ≥ 7 := by omega
    have h_ge : Nat.factorial n ≥ 3 ^ n := h_inductive n h_gt
    -- This contradicts the assumption that n ∈ S
    have h_lt : Nat.factorial n < 3 ^ n := hn
    linarith
  
  -- Combine these to get IsGreatest
  constructor
  · exact h_mem
  · intro n hn
    exact h_upper_bound n hn
