import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: NaturalScaleGapEventually]

theorem NaturalScaleGapEventually :
    ∀ δ : ℝ, 0 < δ →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        1 < δ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
-- BODY
  intro δ hδ
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hn
  have hprod :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' Filter.atTop ?_ hn
    filter_upwards [hlog.eventually_ge_atTop (1 : ℝ)] with n hlog_ge
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_ge hn_nonneg
  have hsqrt :
      Filter.Tendsto
        (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hprod
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ => δ * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
        Filter.atTop Filter.atTop :=
    hsqrt.const_mul_atTop hδ
  exact Filter.eventually_atTop.mp (hscaled.eventually_gt_atTop (1 : ℝ))
