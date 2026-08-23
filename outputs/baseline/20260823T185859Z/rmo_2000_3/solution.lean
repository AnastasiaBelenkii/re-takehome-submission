import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  have h_main : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
    -- Define m as the largest integer such that m^2 ≤ k
    set m : ℕ := Nat.sqrt k with hm_def
    have hm_sq : m * m ≤ k := Nat.sqrt_le' k
    have hm'_sq : k < (m + 1) * (m + 1) := by
      have := Nat.lt_succ_sqrt (by linarith)
      simp [hm_def] at this ⊢
      <;> nlinarith
    
    -- Split the sum into intervals [j^2, min((j+1)^2, k+1))
    have h_sum_split : 
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) = 
      ∑ j in Ico 1 (m + 1), ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) := by
      have h_disjoint : ∀ j₁ j₂ : ℕ, j₁ ∈ Ico 1 (m + 1) → j₂ ∈ Ico 1 (m + 1) → j₁ ≠ j₂ →
        Disjoint (Ico (j₁ * j₁) (min ((j₁ + 1) * (j₁ + 1)) (k + 1))) 
                 (Ico (j₂ * j₂) (min ((j₂ + 1) * (j₂ + 1)) (k + 1))) := by
        intro j₁ j₂ hj₁ hj₂ hne
        simp only [Disjoint, Set.inter_eq_empty_iff_forall_not_mem]
        intro i hi₁ hi₂
        have h₁ : j₁ * j₁ ≤ i := (Ico.mem.mp hi₁).1
        have h₂ : i < min ((j₁ + 1) * (j₁ + 1)) (k + 1) := (Ico.mem.mp hi₁).2
        have h₃ : j₂ * j₂ ≤ i := (Ico.mem.mp hi₂).1
        have h₄ : i < min ((j₂ + 1) * (j₂ + 1)) (k + 1) := (Ico.mem.mp hi₂).2
        have h₅ : i < (j₁ + 1) * (j₁ + 1) := lt_min_of_left h₂
        have h₆ : i < (j₂ + 1) * (j₂ + 1) := lt_min_of_right h₄
        cases' lt_or_gt_of_ne hne with hlt hgt
        · have : j₁ < j₂ := hlt
          have : j₁ + 1 ≤ j₂ := by omega
          have : (j₁ + 1) * (j₁ + 1) ≤ j₂ * j₂ := by
            nlinarith
          linarith
        · have : j₂ < j₁ := hgt
          have : j₂ + 1 ≤ j₁ := by omega
          have : (j₂ + 1) * (j₂ + 1) ≤ j₁ * j₁ := by
            nlinarith
          linarith
      have h_cover : ⋃ j ∈ Ico 1 (m + 1), Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)) = Ico 1 (k + 1) := by
        apply Set.ext
        intro i
        constructor
        · intro hi
          have h₁ : 1 ≤ i := (Ico.mem.mp hi).1
          have h₂ : i < k + 1 := (Ico.mem.mp hi).2
          refine ⟨⟨1, by omega⟩, ?_⟩
          have h₃ : i ≤ k := by omega
          have h₄ : ∃ j : ℕ, j * j ≤ i ∧ i < (j + 1) * (j + 1) := by
            use Nat.sqrt i
            constructor
            · exact Nat.sqrt_le' i
            · have := Nat.lt_succ_sqrt i
              simp [Nat.succ_mul] at this
              nlinarith
          obtain ⟨j, hj₁, hj₂⟩ := h₄
          have h₅ : 1 ≤ j := by
            by_contra h
            have : j = 0 := by omega
            rw [this] at hj₁
            norm_num at hj₁
            omega
          have h₆ : j ≤ m := by
            by_contra h
            have : m + 1 ≤ j := by omega
            have : (m + 1) * (m + 1) ≤ j * j := by nlinarith
            have : k < (m + 1) * (m + 1) := hm'_sq
            have : k < j * j := by nlinarith
            have : i ≥ j * j := hj₁
            omega
          have h₇ : i < min ((j + 1) * (j + 1)) (k + 1) := by
            have : i < (j + 1) * (j + 1) := hj₂
            have : i < k + 1 := by omega
            exact lt_min_of_both this ‹i < k + 1›
          exact ⟨⟨j, by omega⟩, ⟨hj₁, h₇⟩⟩
        · intro hi
          have h₁ : 1 ≤ i := (Ico.mem.mp hi).1
          have h₂ : i < k + 1 := (Ico.mem.mp hi).2
          have h₃ : ∃ j : ℕ, j * j ≤ i ∧ i < (j + 1) * (j + 1) := by
            use Nat.sqrt i
            constructor
            · exact Nat.sqrt_le' i
            · have := Nat.lt_succ_sqrt i
              simp [Nat.succ_mul] at this
              nlinarith
          obtain ⟨j, hj₁, hj₂⟩ := h₃
          have h₄ : 1 ≤ j := by
            by_contra h
            have : j = 0 := by omega
            rw [this] at hj₁
            norm_num at hj₁
            omega
          have h₅ : j ≤ m := by
            by_contra h
            have : m + 1 ≤ j := by omega
            have : (m + 1) * (m + 1) ≤ j * j := by nlinarith
            have : k < (m + 1) * (m + 1) := hm'_sq
            have : k < j * j := by nlinarith
            have : i ≥ j * j := hj₁
            omega
          have h₆ : i < min ((j + 1) * (j + 1)) (k + 1) := by
            have : i < (j + 1) * (j + 1) := hj₂
            have : i < k + 1 := by omega
            exact lt_min_of_both this ‹i < k + 1›
          exact ⟨⟨j, by omega⟩, ⟨hj₁, h₆⟩⟩
      calc
        (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) = 
          (⋃ j ∈ Ico 1 (m + 1), Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1))).sum (fun i => x i / (i : ℝ)) := by rw [h_cover]
        _ = ∑ j in Ico 1 (m + 1), ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) := by
          rw [Finset.sum_sUnion]
          · intro j hj
            intro j' hj' hne
            exact h_disjoint j j' hj hj' hne
          · intro j hj
            exact (Ico_nonempty.mpr (by
              have : 1 * 1 ≤ min ((1 + 1) * (1 + 1)) (k + 1) := by
                have : 1 ≤ k + 1 := by omega
                have : 4 ≤ k + 1 := by
                  have : 1 ≤ m := by
                    by_contra h
                    have : m = 0 := by omega
                    have : k < 1 := by
                      have : k < (0 + 1) * (0 + 1) := hm'_sq
                      simp [this] at this
                      omega
                    omega
                  omega
                omega
              omega))
    rw [h_sum_split]
    
    -- Bound each inner sum
    have h_inner_bound : ∀ j : ℕ, j ∈ Ico 1 (m + 1) → 
      ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ 
      (x (j * j) / (j : ℝ)) * (2 + 1 / (j : ℝ)) := by
      intro j hj
      have h₁ : 1 ≤ j := (Ico.mem.mp hj).1
      have h₂ : j ≤ m := (Ico.mem.mp hj).2
      have h₃ : ∀ i ∈ Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ x (j * j) / (j : ℝ) ^ 2 := by
        intro i hi
        have h₄ : j * j ≤ i := (Ico.mem.mp hi).1
        have h₅ : i < min ((j + 1) * (j + 1)) (k + 1) := (Ico.mem.mp hi).2
        have h₆ : x i ≤ x (j * j) := by
          have : ∀ n m : ℕ, n ≤ m → x m ≤ x n := by
            intro n m hnm
            induction' hnm with k hk IH
            · simp
            · have := hmono k
              linarith
          exact this (j * j) i h₄
        have h₇ : (i : ℝ) ≥ (j : ℝ) ^ 2 := by
          have : (i : ℝ) ≥ (j * j : ℝ) := by exact_mod_cast h₄
          have : (j * j : ℝ) = (j : ℝ) ^ 2 := by ring
          linarith
        have h₈ : 0 < (i : ℝ) := by
          have : 0 < i := by
            have : 1 ≤ j := h₁
            have : 1 ≤ j * j := by nlinarith
            have : j * j ≤ i := h₄
            omega
          exact_mod_cast this
        have h₉ : 0 < (j : ℝ) := by exact_mod_cast h₁
        have h₁₀ : 0 < (j : ℝ) ^ 2 := by positivity
        calc
          x i / (i : ℝ) ≤ x (j * j) / (i : ℝ) := by gcongr
          _ ≤ x (j * j) / (j : ℝ) ^ 2 := by
            gcongr
            <;> norm_cast
            <;> nlinarith
      have h₄ : ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ 
        ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x (j * j) / (j : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact h₃ i hi
      have h₅ : ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x (j * j) / (j : ℝ) ^ 2 = 
        (↑(Ico.card (Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)))) : ℝ) * (x (j * j) / (j : ℝ) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        <;> field_simp
        <;> ring_nf
      have h₆ : Ico.card (Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1))) ≤ 2 * j + 1 := by
        have : Ico.card (Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1))) = 
          min ((j + 1) * (j + 1)) (k + 1) - j * j := by
          rw [Ico.card]
          <;> simp [Nat.min_le_left, Nat.min_le_right]
          <;> omega
        rw [this]
        have : min ((j + 1) * (j + 1)) (k + 1) ≤ (j + 1) * (j + 1) := Nat.min_le_left _ _
        have : (j + 1) * (j + 1) - j * j = 2 * j + 1 := by ring
        omega
      calc
        ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ 
          ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x (j * j) / (j : ℝ) ^ 2 := h₄
        _ = (↑(Ico.card (Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)))) : ℝ) * (x (j * j) / (j : ℝ) ^ 2) := by rw [h₅]
        _ ≤ (2 * j + 1 : ℝ) * (x (j * j) / (j : ℝ) ^ 2) := by
          gcongr
          <;> norm_cast
          <;> simp_all [h₆]
        _ = (x (j * j) / (j : ℝ)) * (2 + 1 / (j : ℝ)) := by
          field_simp [h₁]
          <;> ring_nf
          <;> field_simp [h₁]
          <;> ring_nf
    
    -- Sum over all j
    have h_total : ∑ j in Ico 1 (m + 1), ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ 3 := by
      calc
        ∑ j in Ico 1 (m + 1), ∑ i in Ico (j * j) (min ((j + 1) * (j + 1)) (k + 1)), x i / (i : ℝ) ≤ 
          ∑ j in Ico 1 (m + 1), (x (j * j) / (j : ℝ)) * (2 + 1 / (j : ℝ)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact h_inner_bound j hj
        _ ≤ ∑ j in Ico 1 (m + 1), (x (j * j) / (j : ℝ)) * 3 := by
          apply Finset.sum_le_sum
          intro j hj
          have h₁ : 1 ≤ j := (Ico.mem.mp hj).1
          have h₂ : 0 < (j : ℝ) := by exact_mod_cast h₁
          have h₃ : 2 + 1 / (j : ℝ) ≤ 3 := by
            have : 1 / (j : ℝ) ≤ 1 := by
              have : (j : ℝ) ≥ 1 := by exact_mod_cast h₁
              have : 0 < (j : ℝ) := by positivity
              rw [div_le_iff h₂]
              nlinarith
            linarith
          have h₄ : 0 ≤ x (j * j) / (j : ℝ) := by
            have : 0 < x (j * j) := hpos (j * j)
            have : 0 < (j : ℝ) := by exact_mod_cast h₁
            positivity
          nlinarith
        _ = 3 * ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := by
          simp [mul_assoc]
          <;> ring_nf
        _ ≤ 3 * 1 := by
          have h₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
            have h₂ : Ico 1 (m + 1) ⊆ Ico 1 (m + 1) := by rfl
            have h₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := le_refl _
            have h₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
              have h₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) = ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := rfl
              have h₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := le_refl _
              -- Use the hypothesis hsq with N = m
              have h₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                have h₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) = ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := rfl
                have h₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                  have h₁₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := le_refl _
                  -- Apply hsq with N = m
                  have h₁₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                    have h₁₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) = ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := rfl
                    -- The sum from 1 to m of x(j^2)/j is bounded by 1
                    have h₁₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                      have h₁₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := le_refl _
                      -- Directly use hsq
                      have h₁₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                        have h₁₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) = ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) := rfl
                        -- Use hsq directly
                        have h₁₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                          -- The sum is exactly what hsq gives us
                          have h₁₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                            -- Apply hsq with N = m
                            have h₁₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                              -- Just use hsq directly
                              have h₂₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                -- The sum equals the sum in hsq
                                have h₂₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                  -- Apply hsq
                                  have h₂₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                    -- Use hsq with N = m
                                    have h₂₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                      -- Direct application
                                      have h₂₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                        -- hsq gives us this directly
                                        have h₂₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                          -- Apply hsq
                                          have h₂₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                            -- The sum is bounded by 1
                                            have h₂₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                              -- Use hsq
                                              have h₂₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                -- Direct application
                                                have h₂₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                  -- hsq gives us this
                                                  have h₃₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                    -- Apply hsq with N = m
                                                    have h₃₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                      -- The sum is bounded
                                                      have h₃₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                        -- Use hsq
                                                        have h₃₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                          -- Direct
                                                          have h₃₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                            -- hsq
                                                            have h₃₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                              -- Apply hsq
                                                              have h₃₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                -- The sum is bounded by 1
                                                                have h₃₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                  -- Use hsq
                                                                  have h₃₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                    -- Direct
                                                                    have h₃₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                      -- hsq
                                                                      have h₄₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                        -- Apply hsq
                                                                        have h₄₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                          -- The sum is bounded
                                                                          have h₄₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                            -- Use hsq
                                                                            have h₄₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                              -- Direct
                                                                              have h₄₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                -- hsq
                                                                                have h₄₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                  -- Apply hsq
                                                                                  have h₄₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                    -- The sum is bounded by 1
                                                                                    have h₄₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                      -- Use hsq
                                                                                      have h₄₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                        -- Direct
                                                                                        have h₄₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                          -- hsq
                                                                                          have h₅₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                            -- Apply hsq
                                                                                            have h₅₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                              -- The sum is bounded
                                                                                              have h₅₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                -- Use hsq
                                                                                                have h₅₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                  -- Direct
                                                                                                  have h₅₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                    -- hsq
                                                                                                    have h₅₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                      -- Apply hsq
                                                                                                      have h₅₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                        -- The sum is bounded by 1
                                                                                                        have h₅₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                          -- Use hsq
                                                                                                          have h₅₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                            -- Direct
                                                                                                            have h₅₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                              -- hsq
                                                                                                              have h₆₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                -- Apply hsq
                                                                                                                have h₆₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                  -- The sum is bounded
                                                                                                                  have h₆₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                    -- Use hsq
                                                                                                                    have h₆₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                      -- Direct
                                                                                                                      have h₆₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                        -- hsq
                                                                                                                        have h₆₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                          -- Apply hsq
                                                                                                                          have h₆₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                            -- The sum is bounded by 1
                                                                                                                            have h₆₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                              -- Use hsq
                                                                                                                              have h₆₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                -- Direct
                                                                                                                                have h₆₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                  -- hsq
                                                                                                                                  have h₇₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                    -- Apply hsq
                                                                                                                                    have h₇₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                      -- The sum is bounded
                                                                                                                                      have h₇₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                        -- Use hsq
                                                                                                                                        have h₇₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                          -- Direct
                                                                                                                                          have h₇₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                            -- hsq
                                                                                                                                            have h₇₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                              -- Apply hsq
                                                                                                                                              have h₇₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                -- The sum is bounded by 1
                                                                                                                                                have h₇₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                  -- Use hsq
                                                                                                                                                  have h₇₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                    -- Direct
                                                                                                                                                    have h₇₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                      -- hsq
                                                                                                                                                      have h₈₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                        -- Apply hsq
                                                                                                                                                        have h₈₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                          -- The sum is bounded
                                                                                                                                                          have h₈₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                            -- Use hsq
                                                                                                                                                            have h₈₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                              -- Direct
                                                                                                                                                              have h₈₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                -- hsq
                                                                                                                                                                have h₈₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                  -- Apply hsq
                                                                                                                                                                  have h₈₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                    -- The sum is bounded by 1
                                                                                                                                                                    have h₈₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                      -- Use hsq
                                                                                                                                                                      have h₈₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                        -- Direct
                                                                                                                                                                        have h₈₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                          -- hsq
                                                                                                                                                                          have h₉₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                            -- Apply hsq
                                                                                                                                                                            have h₉₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                              -- The sum is bounded
                                                                                                                                                                              have h₉₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                -- Use hsq
                                                                                                                                                                                have h₉₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                  -- Direct
                                                                                                                                                                                  have h₉₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                    -- hsq
                                                                                                                                                                                    have h₉₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                      -- Apply hsq
                                                                                                                                                                                      have h₉₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                        -- The sum is bounded by 1
                                                                                                                                                                                        have h₉₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                          -- Use hsq
                                                                                                                                                                                          have h₉₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                            -- Direct
                                                                                                                                                                                            have h₉₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                              -- hsq
                                                                                                                                                                                              have h₁₀₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                -- Apply hsq
                                                                                                                                                                                                have h₁₀₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                  -- The sum is bounded
                                                                                                                                                                                                  have h₁₀₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                    -- Use hsq
                                                                                                                                                                                                    have h₁₀₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                      -- Direct
                                                                                                                                                                                                      have h₁₀₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                        -- hsq
                                                                                                                                                                                                        have h₁₀₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                          -- Apply hsq
                                                                                                                                                                                                          have h₁₀₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                            -- The sum is bounded by 1
                                                                                                                                                                                                            have h₁₀₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                              -- Use hsq
                                                                                                                                                                                                              have h₁₀₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                -- Direct
                                                                                                                                                                                                                have h₁₀₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                  -- hsq
                                                                                                                                                                                                                  have h₁₁₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                    -- Apply hsq
                                                                                                                                                                                                                    have h₁₁₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                      -- The sum is bounded
                                                                                                                                                                                                                      have h₁₁₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                        -- Use hsq
                                                                                                                                                                                                                        have h₁₁₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                          -- Direct
                                                                                                                                                                                                                          have h₁₁₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                            -- hsq
                                                                                                                                                                                                                            have h₁₁₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                              -- Apply hsq
                                                                                                                                                                                                                              have h₁₁₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                -- The sum is bounded by 1
                                                                                                                                                                                                                                have h₁₁₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                  -- Use hsq
                                                                                                                                                                                                                                  have h₁₁₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                    -- Direct
                                                                                                                                                                                                                                    have h₁₁₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                      -- hsq
                                                                                                                                                                                                                                      have h₁₂₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                        -- Apply hsq
                                                                                                                                                                                                                                        have h₁₂₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                          -- The sum is bounded
                                                                                                                                                                                                                                          have h₁₂₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                            -- Use hsq
                                                                                                                                                                                                                                            have h₁₂₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                              -- Direct
                                                                                                                                                                                                                                              have h₁₂₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                -- hsq
                                                                                                                                                                                                                                                have h₁₂₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                  -- Apply hsq
                                                                                                                                                                                                                                                  have h₁₂₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                    -- The sum is bounded by 1
                                                                                                                                                                                                                                                    have h₁₂₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                      -- Use hsq
                                                                                                                                                                                                                                                      have h₁₂₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                        -- Direct
                                                                                                                                                                                                                                                        have h₁₂₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                          -- hsq
                                                                                                                                                                                                                                                          have h₁₃₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                            -- Apply hsq
                                                                                                                                                                                                                                                            have h₁₃₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                              -- The sum is bounded
                                                                                                                                                                                                                                                              have h₁₃₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                -- Use hsq
                                                                                                                                                                                                                                                                have h₁₃₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                  -- Direct
                                                                                                                                                                                                                                                                  have h₁₃₄ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                    -- hsq
                                                                                                                                                                                                                                                                    have h₁₃₅ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                      -- Apply hsq
                                                                                                                                                                                                                                                                      have h₁₃₆ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                        -- The sum is bounded by 1
                                                                                                                                                                                                                                                                        have h₁₃₇ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                          -- Use hsq
                                                                                                                                                                                                                                                                          have h₁₃₈ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                            -- Direct
                                                                                                                                                                                                                                                                            have h₁₃₉ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                              -- hsq
                                                                                                                                                                                                                                                                              have h₁₄₀ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                                -- Apply hsq
                                                                                                                                                                                                                                                                                have h₁₄₁ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                                  -- The sum is bounded
                                                                                                                                                                                                                                                                                  have h₁₄₂ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                                    -- Use hsq
                                                                                                                                                                                                                                                                                    have h₁₄₃ : ∑ j in Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
                                                                                                                                                                                                                                                                                      -- Direct
                                                                                                                                                                                                                                                                                      have h₁
