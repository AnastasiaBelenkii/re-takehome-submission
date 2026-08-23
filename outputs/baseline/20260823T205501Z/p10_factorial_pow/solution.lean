import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- 6 satisfies the inequality
  have h6 : Nat.factorial 6 < 3 ^ 6 := by norm_num
  refine ⟨by simpa using h6, ?_⟩
  intro n hn
  by_contra hle
  have hlt : 6 < n := Nat.lt_of_not_ge hle
  have h7le : 7 ≤ n := Nat.succ_le_of_lt hlt
  -- write `n` as `7 + k`
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h7le
  -- prove `3 ^ (7 + k) ≤ (7 + k)!` by induction on `k`
  have hpowle : (3 ^ (7 + k)) ≤ (7 + k)! := by
    induction k with
    | zero =>
        norm_num
    | succ k ih =>
        have h3le : (3 : ℕ) ≤ 7 + k.succ := by
          have : (3 : ℕ) ≤ 7 := by decide
          exact le_trans this (Nat.le_add_left _ _)
        have : (3 ^ (7 + k)) * 3 ≤ (7 + k)! * (7 + k.succ) :=
          Nat.mul_le_mul ih h3le
        simpa [pow_succ, Nat.factorial_succ,
               Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
               Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have : ¬ Nat.factorial (7 + k) < 3 ^ (7 + k) := by
    exact not_lt.mpr hpowle
  exact this hn
