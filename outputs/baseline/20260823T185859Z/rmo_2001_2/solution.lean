import Mathlib

open Nat

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨m, hm⟩
    have h_p_ge_2 : p ≥ 2 := Nat.Prime.two_le hp
    have h_q_ge_2 : q ≥ 2 := Nat.Prime.two_le hq
    
    by_cases h_eq : p = q
    · exact Or.inl h_eq
    · -- p ≠ q
      have h_ne : p ≠ q := h_eq
      have h_cases : p < q ∨ q < p := lt_or_gt_of_ne h_ne
      
      -- We handle the case p < q. The case q < p is symmetric.
      cases h_cases with
      | inl h_lt =>
        -- Case p < q
        have h_m_pos : m > 0 := by
          nlinarith [pow_pos (by linarith : 0 < p) 2, pow_pos (by linarith : 0 < q) 2]
        
        -- Establish bounds for m
        have h_lower : (p + q)^2 < m^2 := by
          have h1 : (p + q)^2 = p^2 + 2*p*q + q^2 := by ring
          rw [h1]
          nlinarith [mul_pos h_p_ge_2 h_q_ge_2]
        
        have h_upper : m^2 < (p + 2*q)^2 := by
          have h1 : (p + 2*q)^2 = p^2 + 4*p*q + 4*q^2 := by ring
          rw [h1]
          have h2 : p^2 + 7*p*q + q^2 < p^2 + 4*p*q + 4*q^2 := by
            nlinarith [h_lt]
          nlinarith
        
        have h_m_bounds : p + q < m ∧ m < p + 2*q := by
          apply And.intro
          · nlinarith
          · nlinarith
        
        -- Define X = 2p + 7q - 2m
        have h_X_def : 2*p + 7*q - 2*m > 0 := by
          have h1 : 2*m < 2*(p + 2*q) := by nlinarith
          omega
        
        set X := 2*p + 7*q - 2*m with hX_def
        set Y := 2*p + 7*q + 2*m with hY_def
        
        have h_prod : X * Y = 45 * q^2 := by
          calc
            X * Y = (2*p + 7*q - 2*m) * (2*p + 7*q + 2*m) := by rw [hX_def, hY_def]
            _ = (2*p + 7*q)^2 - (2*m)^2 := by ring
            _ = 4*p^2 + 28*p*q + 49*q^2 - 4*m^2 := by ring
            _ = 4*(p^2 + 7*p*q + q^2) + 45*q^2 - 4*m^2 := by ring
            _ = 4*m^2 + 45*q^2 - 4*m^2 := by rw [hm]
            _ = 45 * q^2 := by ring
        
        -- Bounds for X
        have h_X_lower : 3*q < X := by
          have h1 : 2*m < 2*p + 4*q := by nlinarith
          omega
        
        have h_X_upper : X < 5*q := by
          have h1 : 2*m > 2*p + 2*q := by nlinarith
          omega
        
        -- X divides 45*q^2
        have h_X_dvd : X ∣ 45 * q^2 := by
          use Y
          rw [h_prod]
        
        -- Show q does not divide X
        have h_q_not_dvd_X : ¬ q ∣ X := by
          intro h_div
          have h_k : ∃ k, X = k * q := by
            obtain ⟨k, hk⟩ := h_div
            exact ⟨k, by linarith⟩
          obtain ⟨k, hk⟩ := h_k
          have h_k_range : 3 < k ∧ k < 5 := by
            constructor <;> nlinarith
          have h_k_val : k = 4 := by omega
          rw [h_k_val] at hk
          have h_X_val : X = 4 * q := by linarith
          have h_Y_val : Y = 45 * q / 4 := by
            have h1 : X * Y = 45 * q^2 := h_prod
            rw [h_X_val] at h1
            have h2 : 4 * q * Y = 45 * q^2 := by linarith
            have h3 : 4 * Y = 45 * q := by
              apply mul_left_cancel₀ (show (4 * q : ℕ) ≠ 0 by nlinarith [h_q_ge_2])
              linarith
            omega
          have h_Y_int : 4 ∣ 45 * q := by
            have h1 : 4 * Y = 45 * q := by
              have h2 : X * Y = 45 * q^2 := h_prod
              rw [h_X_val] at h2
              linarith
            omega
          have h_4_dvd_q : 4 ∣ q := by
            have h1 : 4 ∣ 45 * q := h_Y_int
            have h2 : Nat.Coprime 4 45 := by decide
            exact Nat.Coprime.dvd_mul_right h2 h1
          have h_q_prime : Nat.Prime q := hq
          have h_q_ge_2 : q ≥ 2 := Nat.Prime.two_le hq
          have h_q_not_4 : ¬ 4 ∣ q := by
            intro h
            have h2 : q ≥ 4 := by omega
            have h3 : q % 4 = 0 := by omega
            have h4 : q = 2 := by
              have h5 := Nat.Prime.eq_two_or_odd hq
              cases' h5 with h5 h5
              · exact h5
              · omega
            omega
          contradiction
        
        -- Since q does not divide X, X must divide 45
        have h_X_dvd_45 : X ∣ 45 := by
          have h1 : X ∣ 45 * q^2 := h_X_dvd
          have h2 : ¬ q ∣ X := h_q_not_dvd_X
          -- If q does not divide X, then gcd(X, q) = 1
          have h_gcd : Nat.gcd X q = 1 := by
            have h3 : Nat.Prime q := hq
            have h4 : ¬ q ∣ X := h2
            have h5 : Nat.gcd X q = 1 := by
              have h6 := Nat.Prime.coprime_iff_dvd h3
              simp [h4] at h6 ⊢
              tauto
            exact h5
          -- Since gcd(X, q) = 1, X divides 45
          have h7 : X ∣ 45 := by
            have h8 : X ∣ 45 * q^2 := h1
            have h9 : Nat.Coprime X q := by
              rw [Nat.coprime_iff_gcd_eq_one]
              exact h_gcd
            exact Nat.Coprime.dvd_mul_right h9 h8
          exact h7
        
        -- Check divisors of 45 in range (3q, 5q)
        have h_final : p = 3 ∧ q = 11 := by
          have h_divisors : X ∈ ({1, 3, 5, 9, 15, 45} : Finset ℕ) := by
            have h1 : X ∣ 45 := h_X_dvd_45
            have h2 : X ≤ 45 := Nat.le_of_dvd (by norm_num) h1
            interval_cases X <;> norm_num at h1 ⊢ <;> try contradiction
            <;> try { aesop }
          rcases h_divisors with (rfl | rfl | rfl | rfl | rfl | rfl)
          · -- X = 1
            exfalso
            have h1 : 3*q < 1 := by omega
            have h2 : q ≥ 2 := h_q_ge_2
            omega
          · -- X = 3
            exfalso
            have h1 : 3*q < 3 := by omega
            have h2 : q ≥ 2 := h_q_ge_2
            omega
          · -- X = 5
            exfalso
            have h1 : 3*q < 5 := by omega
            have h2 : q ≥ 2 := h_q_ge_2
            omega
          · -- X = 9
            exfalso
            have h1 : 3*q < 9 := by omega
            have h2 : q ≥ 2 := h_q_ge_2
            omega
          · -- X = 15
            have h1 : 3*q < 15 := by omega
            have h2 : 15 < 5*q := by omega
            have h3 : q < 5 := by omega
            have h4 : q = 3 := by
              have h5 : q ≥ 2 := h_q_ge_2
              interval_cases q <;> norm_num at hq ⊢ <;> try contradiction
            subst h4
            have h5 : X = 15 := by rfl
            have h6 : Y = 27 := by
              have h7 : X * Y = 45 * q^2 := h_prod
              rw [h5]
              norm_num
              omega
            have h7 : 2*p + 7*q - 2*m = 15 := by rw [hX_def, h5]
            have h8 : 2*p + 7*q + 2*m = 27 := by rw [hY_def, h6]
            have h9 : 4*p + 14*q = 42 := by
              have h10 : (2*p + 7*q - 2*m) + (2*p + 7*q + 2*m) = 15 + 27 := by
                linarith
              linarith
            have h10 : 4*p + 42 = 42 := by
              rw [h4] at h9
              linarith
            have h11 : p = 0 := by omega
            have h12 : p ≥ 2 := h_p_ge_2
            omega
          · -- X = 45
            have h1 : 3*q < 45 := by omega
            have h2 : 45 < 5*q := by omega
            have h3 : q > 9 := by omega
            have h4 : q = 11 := by
              have h5 : q ≥ 2 := h_q_ge_2
              have h6 : X ∣ 45 := h_X_dvd_45
              have h7 : 45 < 5*q := by omega
              have h8 : q < 15 := by
                have h9 : 45 < 5*q := by omega
                omega
              interval_cases q <;> norm_num at hq ⊢ <;> try contradiction
            subst h4
            have h5 : X = 45 := by rfl
            have h6 : Y = 121 := by
              have h7 : X * Y = 45 * q^2 := h_prod
              rw [h5]
              norm_num
              omega
            have h7 : 2*p + 7*q - 2*m = 45 := by rw [hX_def, h5]
            have h8 : 2*p + 7*q + 2*m = 121 := by rw [hY_def, h6]
            have h9 : 4*p + 14*q = 166 := by
              have h10 : (2*p + 7*q - 2*m) + (2*p + 7*q + 2*m) = 45 + 121 := by
                linarith
              linarith
            have h10 : 4*p + 154 = 166 := by
              rw [h4] at h9
              linarith
            have h11 : 4*p = 12 := by omega
            have h12 : p = 3 := by omega
            exact ⟨h12, rfl⟩
        exact Or.inr (Or.inr ⟨h_final.1.symm, h_final.2.symm⟩)
      | inr h_lt =>
        -- Case q < p
        -- Symmetric to p < q
        have h_swap : ∃ m, q^2 + 7*q*p + p^2 = m^2 := by
          refine' ⟨m, _⟩
          rw [add_comm, add_comm, mul_comm]
          exact hm
        have h_sol : q = p ∨ (q = 3 ∧ p = 11) ∨ (q = 11 ∧ p = 3) := by
          apply h
          exact h_swap
        cases h_sol with
        | inl h_eq =>
          exfalso
          apply h_ne
          linarith
        | inr h_disj =>
          cases h_disj with
          | inl h_pair =>
            have h_p_eq_11 : p = 11 := by omega
            have h_q_eq_3 : q = 3 := by omega
            exact Or.inr (Or.inl ⟨h_q_eq_3.symm, h_p_eq_11.symm⟩)
          | inr h_pair =>
            have h_p_eq_3 : p = 3 := by omega
            have h_q_eq_11 : q = 11 := by omega
            exact Or.inr (Or.inr ⟨h_q_eq_11.symm, h_p_eq_3.symm⟩)
  · -- Backward direction
    intro h
    rcases h with (h_eq | h_pair | h_pair)
    · -- p = q
      use 3*p
      rw [h_eq]
      ring
    · -- p = 3, q = 11
      use 19
      norm_num [h_pair.1, h_pair.2]
    · -- p = 11, q = 3
      use 19
      norm_num [h_pair.1, h_pair.2]
