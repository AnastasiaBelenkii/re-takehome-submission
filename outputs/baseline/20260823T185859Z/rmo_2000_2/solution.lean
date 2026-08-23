import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Basic

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h₁ : x ≤ 9 := by
    by_contra hx'
    have hx'' : x ≥ 10 := by omega
    have h₂ : (x + 2) ^ 3 > x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      cases x with
      | zero => contradiction
      | succ x' =>
        simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h ⊢
        ring_nf at h ⊢
        omega
    have h₃ : y ^ 3 < (x + 2) ^ 3 := by
      rw [h]
      exact h₂
    have h₄ : y < x + 2 := by
      apply Nat.pow_lt_pow_iff.mpr
      constructor <;> omega
    have h₅ : y ≤ x + 1 := by omega
    have h₆ : (x + 1) ^ 3 ≤ x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      have h₇ : y ^ 3 ≤ (x + 1) ^ 3 := by
        gcongr
      rw [h] at h₇
      exact h₇
    cases x with
    | zero => contradiction
    | succ x' =>
      simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h₆ ⊢
      ring_nf at h₆ ⊢
      omega
  interval_cases x <;> norm_num at h ⊢ <;>
    (try omega) <;>
    (try {
      have : y ≤ 15 := by
        nlinarith
      interval_cases y <;> norm_num at h ⊢ <;> omega
    })
