import Mathlib

open BigOperators Real Nat Topology Rat

theorem aime_1984_p1
  (u : ℕ → ℚ)
  (h₀ : ∀ n, u (n + 1) = u n + 1)
  (h₁ : ∑ k ∈ Finset.range 98, u k.succ = 137) :
  ∑ k ∈ Finset.range 49, u (2 * k.succ) = 93 := by
  have h₂ : ∀ n, u n = u 0 + ↑n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [h₀]
      simp [ih, add_assoc]
      <;> ring
  
  have h₃ : ∑ k ∈ Finset.range 98, u (k + 1) = 98 * u 0 + 4851 := by
    calc
      ∑ k ∈ Finset.range 98, u (k + 1) = ∑ k ∈ Finset.range 98, (u 0 + ↑(k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h₂]
      _ = ∑ k ∈ Finset.range 98, (u 0 + (↑k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Nat.cast_add, Nat.cast_one]
      _ = ∑ k ∈ Finset.range 98, u 0 + ∑ k ∈ Finset.range 98, (↑k + 1) := by
        rw [Finset.sum_add_distrib]
      _ = 98 * u 0 + ∑ k ∈ Finset.range 98, (↑k + 1) := by
        simp [Finset.sum_const, Finset.card_range]
      _ = 98 * u 0 + (∑ k ∈ Finset.range 98, ↑k + ∑ k ∈ Finset.range 98, 1) := by
        rw [Finset.sum_add_distrib]
      _ = 98 * u 0 + (∑ k ∈ Finset.range 98, (k : ℚ) + 98) := by
        have h₃₁ : ∑ k ∈ Finset.range 98, (k : ℚ) = 4753 := by
          norm_num [Finset.sum_range_id]
        have h₃₂ : ∑ k ∈ Finset.range 98, (1 : ℚ) = 98 := by
          simp [Finset.sum_const, Finset.card_range]
          <;> norm_num
        rw [h₃₁, h₃₂]
        <;> simp [add_assoc]
      _ = 98 * u 0 + 4851 := by norm_num
  
  have h₄ : u 0 = -4714 / 98 := by
    have h₄₁ : ∑ k ∈ Finset.range 98, u (k + 1) = 137 := by
      simpa [Nat.succ_eq_add_one] using h₁
    have h₄₂ : 98 * u 0 + 4851 = 137 := by
      linarith [h₃, h₄₁]
    have h₄₃ : 98 * u 0 = -4714 := by
      linarith
    have h₄₄ : u 0 = -4714 / 98 := by
      field_simp at h₄₃ ⊢
      <;> linarith
    exact h₄₄
  
  have h₅ : ∑ k ∈ Finset.range 49, u (2 * k + 2) = 49 * u 0 + 2450 := by
    calc
      ∑ k ∈ Finset.range 49, u (2 * k + 2) = ∑ k ∈ Finset.range 49, (u 0 + ↑(2 * k + 2)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [h₂]
      _ = ∑ k ∈ Finset.range 49, (u 0 + (2 * ↑k + 2)) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      _ = ∑ k ∈ Finset.range 49, u 0 + ∑ k ∈ Finset.range 49, (2 * ↑k + 2) := by
        rw [Finset.sum_add_distrib]
      _ = 49 * u 0 + ∑ k ∈ Finset.range 49, (2 * ↑k + 2) := by
        simp [Finset.sum_const, Finset.card_range]
      _ = 49 * u 0 + (2 * ∑ k ∈ Finset.range 49, ↑k + ∑ k ∈ Finset.range 49, 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = 49 * u 0 + (2 * 1176 + 98) := by
        have h₅₁ : ∑ k ∈ Finset.range 49, (k : ℚ) = 1176 := by
          norm_num [Finset.sum_range_id]
        have h₅₂ : ∑ k ∈ Finset.range 49, (2 : ℚ) = 98 := by
          simp [Finset.sum_const, Finset.card_range]
          <;> norm_num
        rw [h₅₁, h₅₂]
        <;> simp [mul_comm]
      _ = 49 * u 0 + 2450 := by norm_num
  
  have h₆ : ∑ k ∈ Finset.range 49, u (2 * k + 2) = 93 := by
    rw [h₅]
    rw [h₄]
    norm_num
  
  have h₇ : ∑ k ∈ Finset.range 49, u (2 * k.succ) = ∑ k ∈ Finset.range 49, u (2 * k + 2) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp [Nat.succ_eq_add_one]
    <;> ring
  
  rw [h₇]
  exact h₆
