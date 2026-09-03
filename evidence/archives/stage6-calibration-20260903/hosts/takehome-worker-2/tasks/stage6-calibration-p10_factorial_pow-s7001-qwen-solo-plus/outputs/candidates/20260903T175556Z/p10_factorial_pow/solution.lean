import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ S
    simp [p10_answer]
    norm_num [Nat.factorial]
  · -- Show ∀ n, n ∈ S → n ≤ 6
    intro n hn
    by_contra h
    -- We have ¬(n ≤ 6), which means n > 6
    have h_gt : n > 6 := Nat.not_le.mp h
    -- Therefore n ≥ 7
    have h_ge_7 : n ≥ 7 := Nat.succ_le_of_lt h_gt
    
    -- Lemma: ∀ k ≥ 7, k! ≥ 3^k
    have h_lemma : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case k = 7
        norm_num [Nat.factorial]
      · -- Inductive step
        simp_all [Nat.factorial, pow_succ]
        -- We need to show (k+1) * 3^k ≥ 3 * 3^k
        -- Which simplifies to k+1 ≥ 3
        have h_k_plus_1_ge_3 : 3 ≤ k + 1 := by linarith
        calc
          Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by simp [Nat.factorial]
          _ ≥ (k + 1) * 3 ^ k := by gcongr <;> assumption
          _ = 3 ^ k * (k + 1) := by ring
          _ ≥ 3 ^ k * 3 := by
            apply Nat.mul_le_mul_left
            exact h_k_plus_1_ge_3
          _ = 3 * 3 ^ k := by ring
          _ = 3 ^ (k + 1) := by ring
    
    -- Apply lemma to n
    have h_fact_ge_pow : Nat.factorial n ≥ 3 ^ n := h_lemma n h_ge_7
    -- Contradiction with hn : n! < 3^n
    exact lt_irrefl _ (lt_of_le_of_lt h_fact_ge_pow hn)
