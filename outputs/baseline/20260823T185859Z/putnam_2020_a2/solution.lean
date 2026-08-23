import Mathlib

abbrev putnam_2020_a2_solution : ℕ → ℕ := fun k => 4 ^ k

theorem putnam_2020_a2
  (k : ℕ) :
  (∑ j in Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j) =
    putnam_2020_a2_solution k := by
  intro k
  have h : ∀ n : ℕ, ∑ j in Finset.Icc 0 n, 2 ^ (n - j) * Nat.choose (n + j) j = 4 ^ n := by
    intro n
    induction' n with n ih
    · simp [Finset.sum_range_succ]
    · rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      simp [Nat.succ_eq_add_one, pow_add, pow_one, mul_add, add_mul, Nat.choose_succ_succ]
      ring_nf
      <;> simp_all [Nat.choose_succ_succ, Nat.add_sub_cancel]
      <;> ring_nf at *
      <;> omega
  exact h k
