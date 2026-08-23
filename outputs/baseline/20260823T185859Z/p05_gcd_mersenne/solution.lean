import Mathlib.NumberTheory.ArithmeticFunction.Basic
import Mathlib.Tactic

/-- What is the greatest common divisor of `2 ^ 1001 - 1` and `2 ^ 1012 - 1`?
Show that it is `2 ^ 11 - 1`. -/
theorem p05_gcd_mersenne : Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1) = 2 ^ 11 - 1 := by
  have h : Nat.gcd 1001 1012 = 11 := by norm_num
  rw [← Nat.gcd_eq_right_iff_dvd]
  rw [← Nat.gcd_eq_left_iff_dvd]
  apply Nat.dvd_of_mod_eq_zero
  simp [h, Nat.pow_mod, Nat.mod_eq_of_lt]
  <;> rfl
