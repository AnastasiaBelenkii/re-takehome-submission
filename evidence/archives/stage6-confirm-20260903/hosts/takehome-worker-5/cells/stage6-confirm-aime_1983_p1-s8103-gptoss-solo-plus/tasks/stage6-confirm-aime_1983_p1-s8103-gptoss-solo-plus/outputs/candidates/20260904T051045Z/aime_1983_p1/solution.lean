import Mathlib

set_option maxHeartbeats 0

open Real

theorem aime_1983_p1 (x y z w : ℕ) (ht : 1 < x ∧ 1 < y ∧ 1 < z) (hw : 0 ≤ w)
    (h0 : Real.log w / Real.log x = 24) (h1 : Real.log w / Real.log y = 40)
    (h2 : Real.log w / Real.log (x * y * z) = 12) :
    Real.log w / Real.log z = 60 := by
  rcases ht with ⟨hx, hy, hz⟩

  -- positivity of the bases (as reals)
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have : (0 : ℕ) < x := lt_trans Nat.zero_lt_one hx
    exact_mod_cast this
  have hypos : (0 : ℝ) < (y : ℝ) := by
    have : (0 : ℕ) < y := lt_trans Nat.zero_lt_one hy
    exact_mod_cast this
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    have : (0 : ℕ) < z := lt_trans Nat.zero_lt_one hz
    exact_mod_cast this

  -- non‑zero proofs needed for `Real.log_mul`
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hxpos
  have hyne : (y : ℝ) ≠ 0 := ne_of_gt hypos
  have hzne : (z : ℝ) ≠ 0 := ne_of_gt hzpos

  -- positivity of the logarithms (so denominators are non‑zero)
  have hxlogpos : 0 < Real.log x := Real.log_pos (by exact_mod_cast hx)
  have hylogpos : 0 < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hzlogpos : 0 < Real.log z := Real.log_pos (by exact_mod_cast hz)

  have hxlogne : Real.log x ≠ 0 := (ne_of_gt hxlogpos)
  have hylogne : Real.log y ≠ 0 := (ne_of_gt hylogpos)
  have hzlogne : Real.log z ≠ 0 := (ne_of_gt hzlogpos)

  -- rewrite `log (x*y*z)` as a sum
  have hlog_mul_xyz : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
    have hxy : Real.log (x * y) = Real.log x + Real.log y :=
      Real.log_mul hxne hyne
    have hxyz : Real.log ((x * y) * z) = Real.log (x * y) + Real.log z :=
      Real.log_mul (by
        have : (x * y : ℝ) ≠ 0 := mul_ne_zero hxne hyne
        exact this) hzne
    simpa [mul_comm, mul_left_comm, mul_assoc, hxy, add_comm, add_left_comm, add_assoc] using hxyz

  -- turn the third equality into a sum denominator
  have h2' : Real.log w / (Real.log x + Real.log y + Real.log z) = 12 := by
    simpa [hlog_mul_xyz] using h2

  have hsum_ne : Real.log x + Real.log y + Real.log z ≠ 0 := by
    have hpos : 0 < Real.log x + Real.log y + Real.log z := by
      linarith
    exact ne_of_gt hpos

  -- turn the three equalities into linear equations
  have h0_mul : Real.log w = 24 * Real.log x :=
    (div_eq_iff hxlogne).mp h0
  have h1_mul : Real.log w = 40 * Real.log y :=
    (div_eq_iff hylogne).mp h1
  have h2_mul : Real.log w = 12 * (Real.log x + Real.log y + Real.log z) :=
    (div_eq_iff hsum_ne).mp h2'

  -- solve for `Real.log z`
  have hgoal : Real.log w = 60 * Real.log z := by
    linarith [h0_mul, h1_mul, h2_mul]

  -- rewrite back as a division statement
  exact (div_eq_iff hzlogne).mpr hgoal
