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
  -- auxiliary lemma: decreasing sequence gives `x b ≤ x a` for `a ≤ b`
  have hmono' : ∀ {a b}, a ≤ b → x b ≤ x a := by
    intro a b h
    induction' h with b hb ih
    · simpa using le_rfl
    · have : x (b + 1) ≤ x b := by
        have := hmono b
        exact this
      exact le_trans ih this
  -- auxiliary lemma: for any `j ≥ 1`, the sum over the block `[j^2,(j+1)^2)` is bounded
  have hblock (j : ℕ) (hj : 1 ≤ j) :
      (Ico (j * j) ((j + 1) * (j + 1))).sum (fun i => x i / (i : ℝ)) ≤
        3 * (x (j * j) / (j : ℝ)) := by
    have hposj : (0 : ℝ) < (j : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hj).pos
    have hposjj : (0 : ℝ) < (j * j : ℝ) := by
      have : (0 : ℝ) < (j : ℝ) := hposj
      simpa using mul_pos this this
    -- each term in the block is bounded by `x (j*j) / (j*j)`
    have hterm :
        ∀ i ∈ Ico (j * j) ((j + 1) * (j + 1)),
          x i / (i : ℝ) ≤ x (j * j) / ((j * j) : ℝ) := by
      intro i hi
      have hleij : (j * j) ≤ i := (mem_Ico).1 hi).1
      have hxle : x i ≤ x (j * j) := hmono' hleij
      have hle1 : (i : ℝ) ≥ (j * j : ℝ) := by exact_mod_cast hleij
      have hleinv : (1 / (i : ℝ)) ≤ (1 / ((j * j) : ℝ)) :=
        (one_div_le_one_div_of_le hposjj hle1).trans_eq (by ring)
      have : x i / (i : ℝ) = x i * (1 / (i : ℝ)) := by field_simp
      have : x (j * j) / ((j * j) : ℝ) = x (j * j) * (1 / ((j * j) : ℝ)) := by field_simp
      calc
        x i / (i : ℝ) = x i * (1 / (i : ℝ)) := by field_simp
        _ ≤ x (j * j) * (1 / (i : ℝ)) := by
          gcongr
          exact hxle
        _ ≤ x (j * j) * (1 / ((j * j) : ℝ)) := by
          gcongr
          exact hleinv
        _ = x (j * j) / ((j * j) : ℝ) := by field_simp
    have hcard : (Ico (j * j) ((j + 1) * (j + 1))).card = 2 * j + 1 := by
      have : ((j + 1) * (j + 1)) - (j * j) = 2 * j + 1 := by
        ring
      simpa [card_Ico, Nat.sub_eq_iff_eq_add, Nat.add_comm, Nat.mul_comm, Nat.mul_add,
        Nat.add_mul, Nat.succ_mul, Nat.mul_succ] using this
    have hsumle :
        (Ico (j * j) ((j + 1) * (j + 1))).sum (fun i => x i / (i : ℝ)) ≤
          ((2 * j + 1) : ℝ) * (x (j * j) / ((j * j) : ℝ)) := by
      refine sum_le_card_nsmul ?_ ?_
      intro i hi
      exact hterm i hi
    have hcalc :
        ((2 * j + 1 : ℝ) * (x (j * j) / ((j * j) : ℝ))) ≤
          3 * (x (j * j) / (j : ℝ)) := by
      have hposx : 0 ≤ x (j * j) := le_of_lt (hpos _)
      have hposj' : (0 : ℝ) < (j : ℝ) := hposj
      have hposjj' : (0 : ℝ) < (j * j : ℝ) := hposjj
      have : ((2 * j + 1 : ℝ) / ((j * j) : ℝ)) ≤ (3 / (j : ℝ)) := by
        have : (2 * (j : ℝ) + 1) ≤ 3 * (j : ℝ) := by
          have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
            intro h; cases h; exact (Nat.not_succ_le_self 0) (by simpa using hj))))
          linarith
        have hden : (0 : ℝ) < (j * j : ℝ) := hposjj'
        have : ((2 * (j : ℝ) + 1) / ((j * j) : ℝ)) ≤ (3 * (j : ℝ) / ((j * j) : ℝ)) := by
          have := div_le_div_of_le hden this
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using this
      have : ((2 * j + 1 : ℝ) * (x (j * j) / ((j * j) : ℝ))) ≤
          (3 / (j : ℝ)) * (x (j * j)) := by
        have := mul_le_mul_of_nonneg_right this hposx
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    exact le_trans hsumle hcalc
  -- split the whole sum into blocks
  have hsplit :
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤
        (Icc 1 (Nat.sqrt k)).sum (fun j => 3 * (x (j * j) / (j : ℝ))) := by
    have hcover : (Ico 1 (k + 1)) ⊆
        (⋃ j ∈ Icc 1 (Nat.sqrt k), Ico (j * j) ((j + 1) * (j + 1))) := by
      intro i hi
      have hi1 : 1 ≤ i := (mem_Ico).1 hi).1
      have hi2 : i ≤ k := (mem_Ico).1 hi).2
      let j := Nat.sqrt i
      have hjle : j * j ≤ i := Nat.sqrt_mul_self_le i
      have hile : i < (j + 1) * (j + 1) := Nat.lt_succ_sqrt i
      have hjpos : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have : i ∈ Ico (j * j) ((j + 1) * (j + 1)) := by
        exact ⟨hjle, hile⟩
      have : j + 1 ∈ Icc 1 (Nat.sqrt k) := by
        have : (j + 1) ≤ Nat.sqrt k + 1 := by
          have : i ≤ k := hi2
          have : (j + 1) ≤ Nat.sqrt k + 1 := by
            have : (j + 1) ≤ Nat.sqrt i + 1 := Nat.le_succ_sqrt i
            exact le_trans this (Nat.le_succ _)
          exact this
        exact ⟨Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
          intro h; cases h; exact (Nat.not_succ_le_self 0) (by simpa using hi1))), this⟩
      exact mem_iUnion.2 ⟨j + 1, mem_iUnion.2 ⟨this, this⟩⟩
    have hdisj :
        Pairwise (Disjoint on fun j : ℕ => Ico (j * j) ((j + 1) * (j + 1))) := by
      intro a ha b hb hne
      rcases ha with ⟨ha1, ha2⟩
      rcases hb with ⟨hb1, hb2⟩
      have hlt : a < b ∨ b < a := lt_or_gt_of_ne hne
      cases hlt with
      | inl hlt =>
        have : (a + 1) * (a + 1) ≤ b * b := by
          have : a + 1 ≤ b := Nat.succ_le_of_lt hlt
          exact Nat.mul_le_mul this this
        exact disjoint_left.mpr (by
          intro x hx hx'
          have hxle : x < (a + 1) * (a + 1) := (mem_Ico).1 hx).2
          have hxge : (b * b) ≤ x := (mem_Ico).1 hx').1 (lt_of_lt_of_le hxle this))
      | inr hgt => exact (hdisj b hb a ha (Ne.symm hne)).symm
    have : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) =
        (⋃ j ∈ Icc 1 (Nat.sqrt k), Ico (j * j) ((j + 1) * (j + 1))).sum
          (fun i => x i / (i : ℝ)) := by
      refine sum_subset (by
        intro i hi hnot
        have : i ∉ (⋃ j ∈ Icc 1 (Nat.sqrt k), Ico (j * j) ((j + 1) * (j + 1))) := hnot
        exact (not_mem_iUnion).1 this).symm
      intro i hi
      have : i ∈ (⋃ j ∈ Icc 1 (Nat.sqrt k), Ico (j * j) ((j + 1) * (j + 1))) :=
        hcover i hi
      exact mem_iUnion.1 this
    -- now bound each block using `hblock`
    have : (⋃ j ∈ Icc 1 (Nat.sqrt k), Ico (j * j) ((j + 1) * (j + 1))).sum
          (fun i => x i / (i : ℝ)) ≤
        (Icc 1 (Nat.sqrt k)).sum (fun j => 3 * (x (j * j) / (j : ℝ))) := by
      refine sum_le_sum ?_
      intro j hj
      have hjpos : 1 ≤ j := (mem_Icc).1 hj).1
      have hbound := hblock j hjpos
      have : (Ico (j * j) ((j + 1) * (j + 1))).sum (fun i => x i / (i : ℝ)) ≤
          3 * (x (j * j) / (j : ℝ)) := hbound
      simpa using this
    simpa [this] using this
  -- use the hypothesis on squares
  have hsq' : (Icc 1 (Nat.sqrt k)).sum (fun j => x (j * j) / (j : ℝ)) ≤ 1 := by
    have := hsq (Nat.sqrt k)
    simpa [Ico, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.one_mul, Nat.mul_one, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
  have : (Icc 1 (Nat.sqrt k)).sum (fun j => 3 * (x (j * j) / (j : ℝ))) ≤ 3 := by
    have hnonneg : (0 : ℝ) ≤ 3 := by norm_num
    have := mul_le_mul_of_nonneg_left hsq' (by norm_num : (0 : ℝ) ≤ 3)
    simpa [Finset.sum_mul] using this
  exact le_trans hsplit this
