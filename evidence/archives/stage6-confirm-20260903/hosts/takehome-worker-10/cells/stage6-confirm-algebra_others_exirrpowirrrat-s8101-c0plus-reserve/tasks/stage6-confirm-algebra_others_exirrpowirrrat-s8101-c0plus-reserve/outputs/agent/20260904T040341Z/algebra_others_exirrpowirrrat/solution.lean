import Mathlib

open Real

theorem algebra_others_exirrpowirrrat :
    ∃ a b, Irrational a ∧ Irrational b ∧ ¬ Irrational (a ^ b) := by
  classical
  -- `s = √2` is irrational.
  have hirr_sqrt2 : Irrational (Real.sqrt 2) := by
    simpa using irrational_sqrt_two
  -- Define `c = s ^ s`.
  set c : ℝ := (Real.sqrt 2) ^ (Real.sqrt 2) with hc
  -- Classical case split on the (ir)rationality of `c`.
  by_cases hirr_c : Irrational c
  · -- Case 1: `c` is irrational.
    -- Take `a = c`, `b = √2`. Then `a ^ b = 2`, a rational number.
    refine ⟨c, Real.sqrt 2, hirr_c, hirr_sqrt2, ?_⟩
    -- Compute `c ^ √2 = 2`.
    have hcalc : c ^ (Real.sqrt 2) = (2 : ℝ) := by
      have hx : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      calc
        c ^ (Real.sqrt 2)
            = ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) := by
              simpa [hc]
        _ = (Real.sqrt 2) ^ ((Real.sqrt 2) * (Real.sqrt 2)) := by
              simpa using (Real.rpow_mul hx (Real.sqrt 2) (Real.sqrt 2)).symm
        _ = (Real.sqrt 2) ^ (2 : ℝ) := by
              have hprod : (Real.sqrt 2) * (Real.sqrt 2) = (2 : ℝ) := by
                simpa using Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
              simpa [hprod]
        _ = (Real.sqrt 2) ^ (2 : ℝ) := rfl
        _ = (Real.sqrt 2) ^ 2 := by
              simpa using (Real.rpow_natCast (Real.sqrt 2) 2).symm
        _ = (Real.sqrt 2) * (Real.sqrt 2) := by
              simpa [pow_two]
        _ = (2 : ℝ) := by
              simpa using Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
    -- Show `¬ Irrational (c ^ √2)` using the rationality of `2`.
    intro hirr_pow
    have : ∃ q : ℚ, (q : ℝ) = c ^ (Real.sqrt 2) := ⟨2, by simpa [hcalc]⟩
    exact hirr_pow this
  · -- Case 2: `c` is rational (i.e., not irrational).
    -- Take `a = √2`, `b = √2`. Then `a ^ b = c`, which is rational.
    refine ⟨Real.sqrt 2, Real.sqrt 2, hirr_sqrt2, hirr_sqrt2, ?_⟩
    intro hirr_pow
    have : Irrational c := by
      simpa [hc] using hirr_pow
    exact hirr_c this
