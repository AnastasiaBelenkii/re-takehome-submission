import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ {n : ℕ | n ! < 3 ^ n}
    norm_num [Nat.factorial]
  · -- Show ∀ n, n ∈ {n : ℕ | n ! < 3 ^ n} → n ≤ 6
    intro n hn
    by_contra h
    push_neg at h
    have h₁ : n ≥ 7 := by omega
    -- Prove that for n ≥ 7, n! ≥ 3^n
    have h₂ : Nat.factorial n ≥ 3 ^ n := by
      have : ∀ k ≥ 7, Nat.factorial k ≥ 3 ^ k := by
        intro k hk
        induction' hk with k hk IH
        · norm_num [Nat.factorial]
        · simp_all [Nat.factorial, pow_succ]
          nlinarith
      exact this n h₁
    -- Contradiction since n! < 3^n but we proved n! ≥ 3^n
    exact hn h₂
