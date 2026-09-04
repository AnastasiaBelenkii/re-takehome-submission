import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z : ℂ)
  (h₀ : f + 3 * z = 11)
  (h₁ : 3 * (f - 1) - 5 * z = -68) :
  f = -10 ∧ z = 7 := by
  -- eliminate `f` to get an equation for `z`
  have h_elim : -14 * z = -98 := by
    linear_combination -3 * h₀ + 1 * h₁
  have h_pos : (14 : ℂ) * z = 98 := by
    simpa [neg_mul, mul_neg, neg_neg] using h_elim
  -- solve for `z`
  have hz : z = 7 := by
    have h14ne : (14 : ℂ) ≠ 0 := by norm_num
    have hz' : z = (98 : ℂ) / 14 := by
      have : z * (14 : ℂ) = 98 := by
        simpa [mul_comm] using h_pos
      exact (eq_div_iff_mul_eq h14ne).mpr this
    have : (98 : ℂ) / 14 = (7 : ℂ) := by norm_num
    simpa [hz'] using this
  -- compute `f` using the first equation
  have hf_val : f = -10 := by
    calc
      f = 11 - 3 * z := (eq_sub_iff_add_eq).mpr h₀
      _ = 11 - 3 * (7 : ℂ) := by simpa [hz]
      _ = -10 := by norm_num
  exact ⟨hf_val, hz⟩
