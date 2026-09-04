import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem aime_1984_p7
  (f : ℤ → ℤ)
  (h₀ : ∀ n, 1000 ≤ n → f n = n - 3)
  (h₁ : ∀ n, n < 1000 → f n = f (f (n + 5))) :
  f 84 = 997 := by
  -- Helper lemmas for specific values
  have h_f_998 : f 998 = 997 := by
    have h₁_998 : f 998 = f (f (998 + 5)) := h₁ 998 (by norm_num)
    have h₂_1003 : f 1003 = 1003 - 3 := h₀ 1003 (by norm_num)
    have h₃_1003 : f 1003 = 1000 := by rw [h₂_1003]; norm_num
    have h₄_1000 : f 1000 = 1000 - 3 := h₀ 1000 (by norm_num)
    have h₅_1000 : f 1000 = 997 := by rw [h₄_1000]; norm_num
    calc
      f 998 = f (f (998 + 5)) := h₁_998
      _ = f (f 1003) := by norm_num
      _ = f 1000 := by rw [h₃_1003]
      _ = 997 := by rw [h₅_1000]

  have h_f_997 : f 997 = 998 := by
    have h₁_997 : f 997 = f (f (997 + 5)) := h₁ 997 (by norm_num)
    have h₂_1002 : f 1002 = 1002 - 3 := h₀ 1002 (by norm_num)
    have h₃_1002 : f 1002 = 999 := by rw [h₂_1002]; norm_num
    have h₄_999 : f 999 = f (f (999 + 5)) := h₁ 999 (by norm_num)
    have h₅_1004 : f 1004 = 1004 - 3 := h₀ 1004 (by norm_num)
    have h₆_1004 : f 1004 = 1001 := by rw [h₅_1004]; norm_num
    have h₇_1001 : f 1001 = 1001 - 3 := h₀ 1001 (by norm_num)
    have h₈_1001 : f 1001 = 998 := by rw [h₇_1001]; norm_num
    calc
      f 997 = f (f (997 + 5)) := h₁_997
      _ = f (f 1002) := by norm_num
      _ = f 999 := by rw [h₃_1002]
      _ = f (f (999 + 5)) := by rw [h₄_999]
      _ = f (f 1004) := by norm_num
      _ = f 1001 := by rw [h₆_1004]
      _ = 998 := by rw [h₈_1001]

  -- General pattern lemma
  have h_main : ∀ k : ℕ, f ((1000 : ℤ) - k) = if k % 2 = 0 then 997 else 998 := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    by_cases hk_le_5 : k ≤ 5
    · -- Base cases k = 0, 1, 2, 3, 4, 5
      interval_cases k <;>
        simp_all [h₀, h₁]
        <;> norm_num
        <;> try { contradiction }
        <;> try { linarith }
    · -- Inductive step k > 5
      have hk_gt_5 : k > 5 := by omega
      
      -- Define m = k - 5
      let m := k - 5
      have hm_pos : m > 0 := by omega
      have hm_lt_k : m < k := by omega
      
      -- Apply IH to m
      have h_ih_m : f ((1000 : ℤ) - m) = 
          if m % 2 = 0 then 997 else 998 := 
        ih m hm_lt_k
      
      -- Calculate f(1000 - k)
      have h_n_lt_1000 : (1000 : ℤ) - k < 1000 := by
        have : (k : ℤ) > 5 := by exact_mod_cast hk_gt_5
        omega
      
      have h_rec : f ((1000 : ℤ) - k) = f (f (((1000 : ℤ) - k) + 5)) := 
        h₁ ((1000 : ℤ) - k) h_n_lt_1000
      
      -- Simplify inner argument
      have h_shift : (((1000 : ℤ) - k) + 5) = (1000 : ℤ) - m := by
        simp [m]
        <;> ring_nf
        <;> omega
      
      have h_inner_val : f (((1000 : ℤ) - k) + 5) = 
          if m % 2 = 0 then 997 else 998 := by
        rw [h_shift]
        exact h_ih_m
      
      -- Evaluate f(inner_val) based on parity of k
      have h_final : f ((1000 : ℤ) - k) = if k % 2 = 0 then 997 else 998 := by
        by_cases h_k_even : k % 2 = 0
        · -- k even
          have h_inner_is_998 : f (((1000 : ℤ) - k) + 5) = 998 := by
            rw [h_inner_val]
            have h_mod_val : m % 2 = 1 := by
              have : k % 2 = 0 := h_k_even
              have : m = k - 5 := rfl
              omega
            simp [h_k_even, h_mod_val]
            <;> norm_num
          calc
            f ((1000 : ℤ) - k) = f (f (((1000 : ℤ) - k) + 5)) := h_rec
            _ = f 998 := by rw [h_inner_is_998]
            _ = 997 := by rw [h_f_998]
          simp [h_k_even]
        · -- k odd
          have h_inner_is_997 : f (((1000 : ℤ) - k) + 5) = 997 := by
            rw [h_inner_val]
            have h_mod_val : m % 2 = 0 := by
              have : k % 2 = 1 := by omega
              have : m = k - 5 := rfl
              omega
            simp [h_k_even, h_mod_val]
            <;> norm_num
          calc
            f ((1000 : ℤ) - k) = f (f (((1000 : ℤ) - k) + 5)) := h_rec
            _ = f 997 := by rw [h_inner_is_997]
            _ = 998 := by rw [h_f_997]
          simp [h_k_even]
      
      exact h_final
  
  -- Apply to k = 916
  have h_84 : f 84 = 997 := by
    have h_val : f ((1000 : ℤ) - 916) = if 916 % 2 = 0 then 997 else 998 := h_main 916
    have h_916_even : (916 : ℕ) % 2 = 0 := by norm_num
    have h_84_val : f ((1000 : ℤ) - 916) = 997 := by
      rw [h_val]
      simp [h_916_even]
    have h_84_eq : (1000 : ℤ) - 916 = 84 := by norm_num
    rw [h_84_eq] at h_84_val
    exact h_84_val

  exact h_84
