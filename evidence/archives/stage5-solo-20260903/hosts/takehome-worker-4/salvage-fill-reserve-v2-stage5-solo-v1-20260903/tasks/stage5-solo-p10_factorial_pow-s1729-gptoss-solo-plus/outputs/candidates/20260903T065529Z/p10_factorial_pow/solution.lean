import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- Helper lemma: for every `n ≥ 7` we have `3 ^ n ≤ n !`. -/
lemma pow_three_le_factorial_of_seven_le {n : ℕ} (h : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  -- we prove the statement by induction on `n` starting from `7`.
  have h_all :
      ∀ {m}, 7 ≤ m → (3 ^ m ≤ Nat.factorial m) := by
    intro m hm
    -- `Nat.le_induction` works for a dependent predicate.
    have :=
      Nat.le_induction (m:=7) (n:=m) hm
        (C := fun k => 3 ^ k ≤ Nat.factorial k)
        (by
          -- base case `k = 7`
          norm_num)
        (by
          intro k hk hk_ineq
          -- we have `k ≥ 7`, hence `3 ≤ k+1`
          have h3 : (3 : ℕ) ≤ k + 1 := by
            have : (3 : ℕ) ≤ k := le_trans (by decide : (3 : ℕ) ≤ 7) hk
            exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt this (by decide))
          -- multiply the induction hypothesis by the new factor
          have := Nat.mul_le_mul h3 hk_ineq (Nat.zero_le _) (Nat.zero_le _)
          simpa [Nat.pow_succ, Nat.factorial_succ] using this)
    exact this
  exact h_all h

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- first, show that `6` belongs to the set
  refine ⟨?mem, ?bound⟩
  · -- `6! = 720` and `3^6 = 729`, so the inequality holds
    norm_num
  · -- any `n` satisfying the inequality must be `≤ 6`
    intro n hn
    by_contra hle
    have hgt : 6 < n := Nat.lt_of_not_ge hle
    have hseven : 7 ≤ n := Nat.succ_le_of_lt hgt
    have hle' : 3 ^ n ≤ Nat.factorial n :=
      pow_three_le_factorial_of_seven_le hseven
    have : Nat.factorial n < Nat.factorial n :=
      Nat.lt_of_lt_of_le hn hle'
    exact (Nat.lt_asymm this this).elim
