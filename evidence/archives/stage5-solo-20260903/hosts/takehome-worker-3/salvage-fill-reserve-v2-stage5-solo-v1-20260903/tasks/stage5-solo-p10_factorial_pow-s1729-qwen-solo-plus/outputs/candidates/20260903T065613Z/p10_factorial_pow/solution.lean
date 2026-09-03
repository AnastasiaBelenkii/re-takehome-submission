import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First, show that 6 ∈ S, i.e., 6! < 3^6
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by decide
  
  -- Second, show that for all n ≥ 7, n! ≥ 3^n
  have h_induction : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 7
      norm_num [Nat.factorial]
    · -- Inductive step: assume k! ≥ 3^k, prove (k+1)! ≥ 3^(k+1)
      simp_all [Nat.factorial, pow_succ]
      nlinarith
  
  constructor
  · -- Show p10_answer ∈ S
    rw [p10_answer]
    exact h_mem
  · -- Show p10_answer is an upper bound of S
    intro n hn
    by_contra h
    -- If n > 6, then n ∉ S by h_induction
    have h_gt_6 : n > 6 := by
      by_contra h_le
      have h_le_6 : n ≤ 6 := by linarith
      interval_cases n <;> norm_num at hn ⊢ <;> contradiction
    have h_ge_7 : n ≥ 7 := by linarith
    have h_fact_ge_pow : Nat.factorial n ≥ 3 ^ n := h_induction n h_ge_7
    -- Contradiction: hn says n! < 3^n, but h_fact_ge_pow says n! ≥ 3^n
    exact lt_irrefl _ (lt_of_le_of_lt h_fact_ge_pow hn)
