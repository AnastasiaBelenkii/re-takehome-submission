import Mathlib

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem algebra_2varlineareq_fp3zeq11_3tfm1m5zeqn68_feqn10_zeq7
  (f z: ℂ)
  (h₀ : f + 3*z = 11)
  (h₁ : 3*(f - 1) - 5*z = -68) :
  f = -10 ∧ z = 7 := by
  have h₁_simp : 3 * f - 5 * z = -65 := by
    calc
      3 * f - 5 * z = 3 * (f - 1) - 5 * z + 3 := by ring
      _ = -68 + 3 := by rw [h₁]
      _ = -65 := by norm_num

  have h₀_mul : 3 * f + 9 * z = 33 := by
    calc
      3 * f + 9 * z = 3 * (f + 3 * z) := by ring
      _ = 3 * 11 := by rw [h₀]
      _ = 33 := by norm_num

  have h_z_eq : 14 * z = 98 := by
    calc
      14 * z = (3 * f + 9 * z) - (3 * f - 5 * z) := by ring
      _ = 33 - (-65) := by rw [h₀_mul, h₁_simp]
      _ = 98 := by norm_num

  have h_z : z = 7 := by
    have h_z_val : 14 * z = 14 * 7 := by
      calc
        14 * z = 98 := h_z_eq
        _ = 14 * 7 := by norm_num
    apply mul_left_cancel₀ (show (14 : ℂ) ≠ 0 by norm_num)
    exact h_z_val

  have h_f : f = -10 := by
    rw [h_z] at h₀
    norm_num at h₀
    -- h₀ : f + 21 = 11
    have h_f_val : f = 11 - 21 := by
      have h₁ : 11 = f + 21 := by rw [h₀]
      rw [← sub_eq_iff_eq_add] at h₁
      -- h₁ : 11 - 21 = f
      rw [h₁.symm]
    rw [h_f_val]
    norm_num

  exact ⟨h_f, h_z⟩
