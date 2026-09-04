import Mathlib

set_option maxHeartbeats 0

open Complex

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z : ℂ)
  (h₀ : f + 3 * z = 11)
  (h₁ : 3 * (f - 1) - 5 * z = -68) :
  f = -10 ∧ z = 7 := by
  -- express `f` in terms of `z`
  have hf_eq : f = 11 - 3 * z := by
    exact eq_sub_of_add_eq h₀
  -- combine the two equations to eliminate `f`
  have h2' : 14 * z + 3 = 101 := by
    linear_combination (3 : ℂ) * h₀ - (1 : ℂ) * h₁
  -- subtract `3` from both sides to obtain `14*z = 98`
  have h_eq : (14 : ℂ) * z = 98 := by
    have htemp := congrArg (fun t : ℂ => t - (3 : ℂ)) h2'
    have hsub : (101 : ℂ) - (3 : ℂ) = (98 : ℂ) := by norm_num
    simpa [hsub] using htemp
  -- solve for `z`
  have hz : z = 7 := by
    have h14ne : (14 : ℂ) ≠ 0 := by norm_num
    have h98 : (14 : ℂ) * (7 : ℂ) = (98 : ℂ) := by norm_num
    have : (14 : ℂ) * z = (14 : ℂ) * (7 : ℂ) := by
      simpa [h98] using h_eq
    exact mul_left_cancel₀ h14ne this
  -- compute `f`
  have hf : f = -10 := by
    calc
      f = 11 - 3 * z := hf_eq
      _ = 11 - 3 * (7 : ℂ) := by simpa [hz]
      _ = -10 := by norm_num
  exact ⟨hf, hz⟩
