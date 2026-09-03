import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First, we verify that 6 satisfies the condition: 6! < 3^6
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by decide
  
  -- Next, we prove that for all n ≥ 7, n! ≥ 3^n using induction
  have h_upper_bound : ∀ n : ℕ, n ≥ 7 → Nat.factorial n ≥ 3 ^ n := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 7
      norm_num [Nat.factorial]
    · -- Inductive step: assume n! ≥ 3^n, prove (n+1)! ≥ 3^(n+1)
      simp_all [Nat.factorial, pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) n]
  
  -- Combine both parts to show 6 is the greatest element
  constructor
  · exact h_mem
  · intro n hn
    by_cases h : n ≤ 6
    · -- If n ≤ 6, then n ≤ 6 is satisfied
      omega
    · -- If n > 6, then n ≥ 7, so n! ≥ 3^n by our lemma
      have h_ge_7 : n ≥ 7 := by omega
      have h_fact_ge_pow : Nat.factorial n ≥ 3 ^ n := h_upper_bound n h_ge_7
      linarith
