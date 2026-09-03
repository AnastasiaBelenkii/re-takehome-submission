import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- First, show that 6 is in the set (6! < 3^6)
  have h_in : Nat.factorial 6 < 3 ^ 6 := by decide
  
  -- Second, show that for all n > 6, n! ≥ 3^n (so they're not in the set)
  have h_upper : ∀ n : ℕ, n > 6 → ¬(Nat.factorial n < 3 ^ n) := by
    intro n hn
    have h_ge_7 : n ≥ 7 := by omega
    
    -- Prove by induction that for all k ≥ 7, k! ≥ 3^k
    have h_main : Nat.factorial n ≥ 3 ^ n := by
      have h_base : Nat.factorial 7 ≥ 3 ^ 7 := by decide
      
      -- Use induction starting from 7
      have h_ind : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
        intro k hk
        induction' hk with k hk IH
        · exact h_base
        · simp [Nat.factorial_succ, pow_succ] at *
          -- Need to show (k+1)! ≥ 3^(k+1) given k! ≥ 3^k and k ≥ 7
          have h_k_ge_7 : k ≥ 7 := by omega
          have h_k_plus_1_ge_3 : k + 1 ≥ 3 := by omega
          
          calc
            Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := by simp [Nat.factorial_succ]
            _ ≥ (k + 1) * 3 ^ k := by gcongr
            _ ≥ 3 * 3 ^ k := by
              exact Nat.mul_le_mul_right (3 ^ k) h_k_plus_1_ge_3
            _ = 3 ^ k * 3 := by rw [mul_comm]
            _ = 3 ^ (k + 1) := by simp [pow_succ]
      
      exact h_ind n h_ge_7
    
    intro h_lt
    linarith [h_main, h_lt]
  
  -- Combine to show IsGreatest
  constructor
  · exact h_in
  · intro n hn
    by_cases h_gt : n > 6
    · exfalso
      have h_not_in : ¬(Nat.factorial n < 3 ^ n) := h_upper n h_gt
      exact h_not_in hn
    · have h_le : n ≤ 6 := by omega
      exact h_le
