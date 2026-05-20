import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Tablet.RamseyScale

-- [TABLET NODE: RamseyScalePositiveCoefficientLogExpansion]

theorem RamseyScalePositiveCoefficientLogExpansion :
    ∀ c : ℝ, 0 < c →
      (fun k : ℕ => Real.log (c * RamseyScale k) / Real.log (k : ℝ)) =ᶠ[Filter.atTop]
        (fun k : ℕ =>
          (2 : ℝ) + Real.log c / Real.log (k : ℝ) -
            Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) := by
-- BODY
  intro c hc
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
  have hk_one_nat : 1 < k := Nat.lt_of_lt_of_le (by decide) hk
  have hk_one_cast : ((1 : ℕ) : ℝ) < (k : ℝ) :=
    (Nat.cast_lt (α := ℝ)).2 hk_one_nat
  have hk_one : (1 : ℝ) < (k : ℝ) := by
    simpa using hk_one_cast
  have hk_pos : 0 < (k : ℝ) := lt_trans zero_lt_one hk_one
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hk_one
  have hlog_ne : Real.log (k : ℝ) ≠ 0 := ne_of_gt hlogpos
  unfold RamseyScale
  rw [Real.log_mul hc.ne' (div_ne_zero (pow_ne_zero 2 hk_ne) hlog_ne),
    Real.log_div (pow_ne_zero 2 hk_ne) hlog_ne, Real.log_pow]
  field_simp [hlog_ne]
  ring
