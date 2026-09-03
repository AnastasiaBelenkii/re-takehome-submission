import Mathlib

open Nat

/-- From `2000 ∣ a ^ 2 * b ^ 5` we get `2 ∣ a * b`. -/
private lemma two_dvd_mul_of_pow (a b : ℕ) (h : 2000 ∣ a ^ 2 * b ^ 5) :
    (2 : ℕ) ∣ a * b := by
  have h2 : (2 : ℕ) ∣ a ^ 2 * b ^ 5 := by
    have : (2 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact dvd_trans this h
  rcases (Nat.prime_two.dvd_mul).1 h2 with h2a | h2b
  ·
    have h2a' : (2 : ℕ) ∣ a := Nat.prime_two.dvd_of_dvd_pow h2a
    exact dvd_mul_of_dvd_left h2a' b
  ·
    have h2b' : (2 : ℕ) ∣ b := Nat.prime_two.dvd_of_dvd_pow h2b
    exact dvd_mul_of_dvd_right h2b' a

/-- From `2000 ∣ a ^ 2 * b ^ 5` we get `5 ∣ a * b`. -/
private lemma five_dvd_mul_of_pow (a b : ℕ) (h : 2000 ∣ a ^ 2 * b ^ 5) :
    (5 : ℕ) ∣ a * b := by
  have h5 : (5 : ℕ) ∣ a ^ 2 * b ^ 5 := by
    have : (5 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact dvd_trans this h
  rcases (Nat.prime_five.dvd_mul).1 h5 with h5a | h5b
  ·
    have h5a' : (5 : ℕ) ∣ a := Nat.prime_five.dvd_of_dvd_pow h5a
    exact dvd_mul_of_dvd_left h5a' b
  ·
    have h5b' : (5 : ℕ) ∣ b := Nat.prime_five.dvd_of_dvd_pow h5b
    exact dvd_mul_of_dvd_right h5b' a

/-- From `2000 ∣ a ^ 3 * b ^ 4` we get `2 ∣ a * b`. -/
private lemma two_dvd_mul_of_pow' (a b : ℕ) (h : 2000 ∣ a ^ 3 * b ^ 4) :
    (2 : ℕ) ∣ a * b := by
  have h2 : (2 : ℕ) ∣ a ^ 3 * b ^ 4 := by
    have : (2 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact dvd_trans this h
  rcases (Nat.prime_two.dvd_mul).1 h2 with h2a | h2b
  ·
    have h2a' : (2 : ℕ) ∣ a := Nat.prime_two.dvd_of_dvd_pow h2a
    exact dvd_mul_of_dvd_left h2a' b
  ·
    have h2b' : (2 : ℕ) ∣ b := Nat.prime_two.dvd_of_dvd_pow h2b
    exact dvd_mul_of_dvd_right h2b' a

/-- From `2000 ∣ a ^ 3 * b ^ 4` we get `5 ∣ a * b`. -/
private lemma five_dvd_mul_of_pow' (a b : ℕ) (h : 2000 ∣ a ^ 3 * b ^ 4) :
    (5 : ℕ) ∣ a * b := by
  have h5 : (5 : ℕ) ∣ a ^ 3 * b ^ 4 := by
    have : (5 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact dvd_trans this h
  rcases (Nat.prime_five.dvd_mul).1 h5 with h5a | h5b
  ·
    have h5a' : (5 : ℕ) ∣ a := Nat.prime_five.dvd_of_dvd_pow h5a
    exact dvd_mul_of_dvd_left h5a' b
  ·
    have h5b' : (5 : ℕ) ∣ b := Nat.prime_five.dvd_of_dvd_pow h5b
    exact dvd_mul_of_dvd_right h5b' a

theorem rmo_2000_6 :
    (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
    (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- first IsLeast
    refine ⟨?mem1, ?least1⟩
    · -- membership of 10
      refine ⟨1, 10, ?pos1, ?pos2, ?dvd1, rfl⟩
      · exact by decide
      · exact by decide
      ·
        have : (2000 : ℕ) ∣ (10 : ℕ) ^ 5 := by
          norm_num
        simpa [one_pow] using this
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : (2 : ℕ) ∣ a * b := two_dvd_mul_of_pow a b hdiv
      have h5 : (5 : ℕ) ∣ a * b := five_dvd_mul_of_pow a b hdiv
      have h10 : (10 : ℕ) ∣ a * b := by
        have : (Nat.lcm 2 5) ∣ a * b := (Nat.lcm_dvd_iff).2 ⟨h2, h5⟩
        have h_eq : Nat.lcm 2 5 = 10 := by
          norm_num
        simpa [h_eq] using this
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
  · -- second IsLeast
    refine ⟨?mem2, ?least2⟩
    · -- membership of 10
      refine ⟨1, 10, ?pos1', ?pos2', ?dvd2, rfl⟩
      · exact by decide
      · exact by decide
      ·
        have : (2000 : ℕ) ∣ (10 : ℕ) ^ 4 := by
          norm_num
        simpa [one_pow] using this
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : (2 : ℕ) ∣ a * b := two_dvd_mul_of_pow' a b hdiv
      have h5 : (5 : ℕ) ∣ a * b := five_dvd_mul_of_pow' a b hdiv
      have h10 : (10 : ℕ) ∣ a * b := by
        have : (Nat.lcm 2 5) ∣ a * b := (Nat.lcm_dvd_iff).2 ⟨h2, h5⟩
        have h_eq : Nat.lcm 2 5 = 10 := by
          norm_num
        simpa [h_eq] using this
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
