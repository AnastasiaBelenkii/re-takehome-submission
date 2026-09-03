import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by norm_num [Nat.factorial]
  
  have h_inductive_step : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 7
      norm_num [Nat.factorial]
    · -- Inductive step: assume k ≥ 7 and k! ≥ 3^k, prove (k+1)! ≥ 3^(k+1)
      simp [Nat.factorial, pow_succ] at *
      have h_k_ge_3 : k + 1 ≥ 3 := by omega
      calc
        (k + 1) * Nat.factorial k ≥ (k + 1) * 3 ^ k := by
          exact Nat.mul_le_mul_left (k + 1) IH
        _ ≥ 3 * 3 ^ k := by
          exact Nat.mul_le_mul_right (3 ^ k) h_k_ge_3
        _ = 3 ^ (k + 1) := by
          rw [Nat.mul_comm, ← Nat.pow_succ]
  
  constructor
  · rw [p10_answer]
    exact h_mem
  · intro n hn
    by_contra h
    have h_gt : n > 6 := Nat.lt_of_not_le h
    have h_ge_7 : n ≥ 7 := by omega
    have h_fact_ge : Nat.factorial n ≥ 3 ^ n := h_inductive_step n h_ge_7
    have h_contra : 3 ^ n < 3 ^ n := lt_of_le_of_lt h_fact_ge hn
    exact lt_irrefl _ h_contra
