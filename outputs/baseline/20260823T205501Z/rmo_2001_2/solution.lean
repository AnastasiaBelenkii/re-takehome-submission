import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  have h5 : Nat.Prime 5 := by norm_num
  constructor
  · rintro ⟨m, hm⟩
    have hpos : 0 < p + q := Nat.add_pos (Nat.succ_le_iff.mp hp.one_lt) (Nat.succ_le_iff.mp hq.one_lt)
    have hpos' : 0 < m := by
      have : p ^ 2 + 7 * p * q + q ^ 2 > 0 := by
        apply Nat.succ_lt_succ_iff.mp
        have : p ^ 2 + 7 * p * q + q ^ 2 ≥ 1 := Nat.succ_le_of_lt (Nat.succ_pos _)
        exact this
      exact Nat.lt_of_lt_of_le (Nat.succ_pos _) (by simpa [hm] using this)
    set a := m - (p + q) with ha
    set b := m + (p + q) with hb
    have hab : a * b = 5 * p * q := by
      have : (m - (p + q)) * (m + (p + q)) = m ^ 2 - (p + q) ^ 2 := by
        ring
      have : a * b = m ^ 2 - (p + q) ^ 2 := by
        simpa [ha, hb] using this
      have : m ^ 2 - (p + q) ^ 2 = 5 * p * q := by
        have : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2 := hm
        have : (p + q) ^ 2 + 5 * p * q = m ^ 2 := by
          simpa [pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
                 mul_comm, mul_left_comm, mul_assoc] using this
        have : m ^ 2 - (p + q) ^ 2 = 5 * p * q := by
          linarith
        exact this
      simpa [this] using this
    have hposab : 0 < a ∧ 0 < b := by
      have h1 : a = m - (p + q) := ha
      have h2 : b = m + (p + q) := hb
      have : p + q < m := by
        have : (p + q) ^ 2 < m ^ 2 := by
          have : (p + q) ^ 2 + 5 * p * q = m ^ 2 := by
            simpa [pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc,
                   mul_comm, mul_left_comm, mul_assoc] using hm
          linarith
        exact Nat.lt_of_pow_lt_pow (Nat.succ_le_iff.mp (Nat.succ_pos _)) this
      have hposa : 0 < a := Nat.sub_pos_of_lt this
      have hposb : 0 < b := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le this (Nat.le_add_left _ _))
        (Nat.le_of_lt (Nat.lt_of_lt_of_le this (Nat.le_add_left _ _)))
      exact ⟨hposa, Nat.succ_pos _⟩
    have hparity : a % 2 = b % 2 := by
      have : b - a = 2 * (p + q) := by
        dsimp [a, b] at *
        ring
      have : (b - a) % 2 = 0 := by
        simpa [Nat.mul_mod, Nat.mod_self] using congrArg (fun n => n % 2) this
      have : (b % 2 - a % 2) % 2 = 0 := by
        simpa [Nat.sub_mod] using this
      have : b % 2 = a % 2 := by
        have h := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
        have : (b % 2 - a % 2) % 2 = 0 := this
        have : b % 2 = a % 2 := by
          have : (b % 2 - a % 2) % 2 = 0 := this
          have : b % 2 = a % 2 := by
            have : (b % 2 - a % 2) % 2 = 0 := this
            exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide : 0 < 2))
          exact this
        exact this
      exact this
    have hdiva : a ∣ 5 * p * q := by
      have : a * b = 5 * p * q := hab
      exact ⟨b, this.symm⟩
    have hdivb : b ∣ 5 * p * q := by
      have : a * b = 5 * p * q := hab
      exact ⟨a, this.symm⟩
    have hcases : a = 1 ∨ a = 5 ∨ a = p ∨ a = q ∨ a = 5 * p ∨ a = 5 * q ∨ a = p * q ∨ a = 5 * p * q := by
      have hprime : (Nat.Prime 5) ∧ (Nat.Prime p) ∧ (Nat.Prime q) := ⟨h5, hp, hq⟩
      rcases hprime with ⟨h5', hp', hq'⟩
      have hfactor : a ∣ 5 * p * q := hdiva
      rcases Nat.dvd_mul.mp hfactor with h5a | hpq
      · rcases Nat.dvd_mul.mp h5a with ha5 | ha'p
        · rcases Nat.dvd_mul.mp ha5 with ha1 | ha5'
          · left; exact ha1
          · right; left; exact ha5'
        · rcases Nat.dvd_mul.mp ha'p with ha'p1 | ha'p2
          · right; right; left; exact ha'p1
          · right; right; right; left; exact ha'p2
      · rcases Nat.dvd_mul.mp hpq with hpq5 | hpq'
        · rcases Nat.dvd_mul.mp hpq5 with hp5 | hq5
          · rcases Nat.dvd_mul.mp hp5 with hp1 | hp5'
            · left; exact hp1
            · right; left; exact hp5'
          · rcases Nat.dvd_mul.mp hq5 with hq1 | hq5'
            · left; exact hq1
            · right; right; left; exact hq5'
        · rcases Nat.dvd_mul.mp hpq' with hpq5' | hpqq
          · rcases Nat.dvd_mul.mp hpq5' with hp5' | hq5'
            · rcases Nat.dvd_mul.mp hp5' with hp1' | hp5''
              · left; exact hp1'
              · right; left; exact hp5''
            · rcases Nat.dvd_mul.mp hq5' with hq1' | hq5''
              · left; exact hq1'
              · right; right; left; exact hq5''
          · rcases Nat.dvd_mul.mp hpqq with hpq5'' | hpq5'''
            · rcases Nat.dvd_mul.mp hpq5'' with hp5'' | hq5'''
              · rcases Nat.dvd_mul.mp hp5'' with hp1'' | hp5''' 
                · left; exact hp1''
                · right; left; exact hp5'''
              · rcases Nat.dvd_mul.mp hq5''' with hq1'' | hq5''''
                · left; exact hq1''
                · right; right; left; exact hq5''''
              · right; right; right; exact hpq5'''
    have hcases' : a = 1 ∨ a = 5 ∨ a = p ∨ a = q ∨ a = 5 * p ∨ a = 5 * q ∨ a = p * q ∨ a = 5 * p * q := hcases
    have hfinal : p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by
      rcases hcases' with h1 | h5 | hp | hq | h5p | h5q | hpq | h5pq
      · -- a = 1
        have : b = 5 * p * q := by
          have : a * b = 5 * p * q := hab
          simpa [h1] using this
        have hbpos : b > 0 := Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos hp.one_lt hq.one_lt)
        have : 2 * (p + q) = b - a := by
          dsimp [a, b] at *
          ring
        have : 2 * (p + q) = 5 * p * q - 1 := by
          simpa [h1] using this
        have : 2 * (p + q) + 1 = 5 * p * q := by linarith
        have hsmall : 5 * p * q ≤ 2 * (p + q) + 1 := by
          have : 5 * p * q = 2 * (p + q) + 1 := by linarith
          exact le_of_eq this
        have : 5 * p * q ≤ 2 * (p + q) + 1 := hsmall
        have hbound : p ≤ 3 ∧ q ≤ 11 ∨ p ≤ 11 ∧ q ≤ 3 := by
          have hp_le : p ≤ 11 := by
            have : 5 * p * q ≤ 2 * (p + q) + 1 := this
            have : 5 * p * q ≤ 4 * (p + q) := by
              linarith
            have : 5 * p * q ≤ 4 * p + 4 * q := by
              simpa [Nat.mul_add] using this
            have : 5 * p * q ≤ 4 * p + 4 * q := this
            have : 5 * p * q ≤ 4 * p + 4 * q := this
            sorry
          sorry
        sorry
      · -- a = 5
        sorry
      · -- a = p
        sorry
      · -- a = q
        sorry
      · -- a = 5 * p
        sorry
      · -- a = 5 * q
        sorry
      · -- a = p * q
        sorry
      · -- a = 5 * p * q
        sorry
    exact hfinal
  · intro h
    rcases h with rfl | h | h
    · refine ⟨3 * p, ?_⟩
      ring
    · rcases h with ⟨hp3, hq11⟩
      subst hp3
      subst hq11
      refine ⟨19, ?_⟩
      norm_num
    · rcases h with ⟨hp11, hq3⟩
      subst hp11
      subst hq3
      refine ⟨19, ?_⟩
      norm_num
