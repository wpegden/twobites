import Tablet.Preamble
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

-- [TABLET NODE: OppositeProjectionTailPowerExponentialBound]

theorem OppositeProjectionTailPowerExponentialBound (A L : ℝ) (t : ℕ)
    (hA0 : 0 ≤ A)
    (hA : A ≤ Real.exp 1 / 50)
    (ht : 100 * L ^ 3 ≤ (t : ℝ)) :
    A ^ t ≤ Real.exp (-(100 * Real.log (50 / Real.exp 1)) * L ^ 3) := by
-- BODY
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp_lt_50 : Real.exp 1 < 50 := by
    linarith [Real.exp_one_lt_three]
  have hratio_pos : 0 < 50 / Real.exp 1 := div_pos (by norm_num) hexp_pos
  have hratio_gt_one : 1 < 50 / Real.exp 1 := by
    rw [lt_div_iff₀ hexp_pos]
    simpa using hexp_lt_50
  have hlog_pos : 0 < Real.log (50 / Real.exp 1) := Real.log_pos hratio_gt_one
  have hbase_nonneg : 0 ≤ Real.exp 1 / 50 := by positivity
  have hpow_base : A ^ t ≤ (Real.exp 1 / 50) ^ t :=
    pow_le_pow_left₀ hA0 hA t
  have hbase_eq : Real.exp 1 / 50 = Real.exp (-Real.log (50 / Real.exp 1)) := by
    rw [Real.exp_neg, Real.exp_log hratio_pos]
    field_simp [hexp_pos.ne']
  have hpow_eq :
      (Real.exp 1 / 50) ^ t =
        Real.exp (-(Real.log (50 / Real.exp 1)) * (t : ℝ)) := by
    rw [hbase_eq]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexponent_le :
      -(Real.log (50 / Real.exp 1)) * (t : ℝ) ≤
        -(100 * Real.log (50 / Real.exp 1)) * L ^ 3 := by
    have hmul :
        Real.log (50 / Real.exp 1) * (100 * L ^ 3) ≤
          Real.log (50 / Real.exp 1) * (t : ℝ) :=
      mul_le_mul_of_nonneg_left ht hlog_pos.le
    nlinarith
  calc
    A ^ t ≤ (Real.exp 1 / 50) ^ t := hpow_base
    _ = Real.exp (-(Real.log (50 / Real.exp 1)) * (t : ℝ)) := hpow_eq
    _ ≤ Real.exp (-(100 * Real.log (50 / Real.exp 1)) * L ^ 3) :=
      Real.exp_le_exp.mpr hexponent_le
