import Mathlib

set_option maxHeartbeats 0

open Complex

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z : ℂ)
  (h₀ : f + 3 * z = 11)
  (h₁ : 3 * (f - 1) - 5 * z = -68) :
  f = -10 ∧ z = 7 := by
  -- simplify the second equation
  have h₁' : 3 * f - 5 * z = -65 := by
    calc
      3 * f - 5 * z = (3 * (f - 1) - 5 * z) + 3 := by ring
      _ = -68 + 3 := by simpa [h₁]
      _ = -65 := by norm_num
  -- combine the two equations to eliminate `f`
  have h₂ : 14 * z = 98 := by
    linear_combination (3 : ℂ) * h₀ - h₁'
  -- solve for `z`
  have hz : z = 7 := by
    have h14ne : (14 : ℂ) ≠ 0 := by norm_num
    have hz' : z = (98 : ℂ) / 14 :=
      (eq_div_iff_mul_eq h14ne).mpr (by
        simpa [mul_comm] using h₂)
    have hval : (98 : ℂ) / 14 = (7 : ℂ) := by norm_num
    simpa [hval] using hz'
  -- solve for `f`
  have hf : f = -10 := by
    have htemp : f = 11 - 3 * z := eq_sub_of_add_eq h₀
    have htemp2 : f = 11 - 3 * 7 := by
      simpa [hz] using htemp
    have hval : (11 : ℂ) - 3 * 7 = (-10 : ℂ) := by norm_num
    simpa [hval] using htemp2
  exact ⟨hf, hz⟩
