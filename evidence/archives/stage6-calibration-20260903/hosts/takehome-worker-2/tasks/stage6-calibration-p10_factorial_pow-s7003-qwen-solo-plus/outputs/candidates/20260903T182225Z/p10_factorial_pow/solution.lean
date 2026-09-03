import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove 6! < 3^6
    norm_num [Nat.factorial]
  · -- Prove ∀ n, n! < 3^n → n ≤ 6
    intro n hn
    by_contra h
    -- If n > 6, then n ≥ 7
    have h_gt_6 : n > 6 := Nat.lt_of_not_le h
    have h_ge_7 : n ≥ 7 := Nat.succ_le_iff.mpr h_gt_6
    
    -- Lemma: for all k ≥ 7, k! ≥ 3^k
    have h_main : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step: assume for k, prove for k+1
        simp_all [Nat.factorial, pow_succ]
        calc
          (k + 1) * Nat.factorial k ≥ (k + 1) * 3 ^ k := by
            apply Nat.mul_le_mul_left (k + 1)
            exact IH
          _ ≥ 3 * 3 ^ k := by
            apply Nat.mul_le_mul_right (3 ^ k)
            omega
          _ = 3 ^ k * 3 := by rw [Nat.mul_comm]
          _ = 3 ^ (k + 1) := by rw [← pow_succ]
    
    -- Apply the main lemma to get contradiction
    have h_fact_ge_pow : Nat.factorial n ≥ 3 ^ n := h_main n h_ge_7
    -- This contradicts hn : n! < 3^n
    exact Nat.not_lt_of_le h_fact_ge_pow hn
