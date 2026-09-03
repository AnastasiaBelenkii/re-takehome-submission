import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Verify that 6! < 3^6
    norm_num [Nat.factorial]
  · -- Prove that for all n in the set, n ≤ 6
    intro n hn
    by_contra h
    -- Assume n > 6, derive contradiction
    have h_gt_6 : n ≥ 7 := by
      have h' : ¬(n ≤ 6) := h
      have h'' : n ≥ 7 := by
        by_contra h'''
        -- If n < 7, then n ≤ 6
        have h'''' : n ≤ 6 := by
          omega
        exact h' h''''
      exact h''
    -- Show that for all k ≥ 7, k! ≥ 3^k
    have h_main : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step: assume k! ≥ 3^k, prove (k+1)! ≥ 3^(k+1)
        simp_all [Nat.factorial, pow_succ]
        nlinarith
    -- Apply to our n
    have h_n_fact_ge_3pow : Nat.factorial n ≥ 3 ^ n := h_main n h_gt_6
    -- Contradiction with hn : n! < 3^n
    have h_lt : Nat.factorial n < 3 ^ n := hn
    linarith
