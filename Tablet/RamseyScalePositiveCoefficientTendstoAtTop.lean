import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.RamseyScale

-- [TABLET NODE: RamseyScalePositiveCoefficientTendstoAtTop]

theorem RamseyScalePositiveCoefficientTendstoAtTop :
    ∀ c : ℝ, 0 < c →
      Filter.Tendsto (fun k : ℕ => c * RamseyScale k) Filter.atTop Filter.atTop := by
-- BODY
  intro c hc
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc)
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with k hk
  have hk_one_nat : 1 < k := Nat.lt_of_lt_of_le (by decide) hk
  have hk_one_cast : ((1 : ℕ) : ℝ) < (k : ℝ) :=
    (Nat.cast_lt (α := ℝ)).2 hk_one_nat
  have hk_one : (1 : ℝ) < (k : ℝ) := by
    simpa using hk_one_cast
  have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hk_one
  have hlog_le : Real.log (k : ℝ) ≤ (k : ℝ) := Real.log_le_self hk_nonneg
  have hscale_ge : (k : ℝ) ≤ RamseyScale k := by
    unfold RamseyScale
    rw [le_div_iff₀ hlogpos]
    have hmul : (k : ℝ) * Real.log (k : ℝ) ≤ (k : ℝ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hlog_le hk_nonneg
    simpa [pow_two] using hmul
  exact mul_le_mul_of_nonneg_left hscale_ge (le_of_lt hc)
