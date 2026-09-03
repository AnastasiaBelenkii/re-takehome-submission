import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First, we need to show that 6 ∈ {n : ℕ | n! < 3^n}, i.e., 6! < 3^6
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by norm_num [Nat.factorial]
  
  -- Second, we need to show that for all n > 6, n! ≥ 3^n
  -- We prove this by induction on n starting from 7.
  have h_inductive_step : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
    intro k hk
    induction' hk with k hk IH
    · -- Base case: k = 7
      norm_num [Nat.factorial]
    · -- Inductive step: assume k! ≥ 3^k, prove (k+1)! ≥ 3^(k+1)
      -- Note: hk here is k ≥ 7 (from Nat.le.induction structure)
      -- IH is Nat.factorial k ≥ 3 ^ k
      simp_all [Nat.factorial, pow_succ]
      -- We need to show (k + 1) * 3^k ≥ 3 * 3^k
      -- Since k ≥ 7, k + 1 ≥ 8 > 3.
      nlinarith [hk, pow_pos (by norm_num : (0 : ℕ) < 3) k]
  
  -- Combine both parts to show IsGreatest
  constructor
  · -- Show p10_answer ∈ S
    rw [p10_answer]
    exact h_mem
  · -- Show p10_answer is an upper bound
    intro n hn
    by_contra h
    -- Assume ¬(n ≤ 6), which implies n > 6
    have h_gt : n > 6 := by omega
    -- Now we have n > 6, so n >= 7
    have h_ge_7 : n ≥ 7 := by omega
    
    -- Apply the inductive result
    have h_fact_ge : Nat.factorial n ≥ 3 ^ n := h_inductive_step n h_ge_7
    
    -- Contradiction with hn : n! < 3^n
    have h_false : False := by
      have h_not_lt : ¬(Nat.factorial n < 3 ^ n) := by
        intro h_lt
        linarith [h_fact_ge, h_lt]
      exact h_not_lt hn
      
    exact h_false
