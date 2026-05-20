import Tablet.LogLogNatOverLogNatTendstoZero
import Tablet.RamseyScale
import Tablet.RamseyScalePositiveCoefficientLogExpansion

-- [TABLET NODE: RamseyScalePositiveCoefficientLogRatio]

theorem RamseyScalePositiveCoefficientLogRatio :
    ∀ c : ℝ, 0 < c →
      Filter.Tendsto
        (fun k : ℕ => Real.log (c * RamseyScale k) / Real.log (k : ℝ))
        Filter.atTop (nhds (2 : ℝ)) := by
-- BODY
  intro c hc
  have hlog_atTop :
      Filter.Tendsto (fun k : ℕ => Real.log (k : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst :
      Filter.Tendsto
        (fun k : ℕ => Real.log c / Real.log (k : ℝ))
        Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hlog_atTop
  have hexpanded :
      Filter.Tendsto
        (fun k : ℕ =>
          (2 : ℝ) + Real.log c / Real.log (k : ℝ) -
            Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))
        Filter.atTop (nhds (2 : ℝ)) := by
    simpa using
      (tendsto_const_nhds.add hconst).sub LogLogNatOverLogNatTendstoZero
  exact
    (Filter.tendsto_congr' (RamseyScalePositiveCoefficientLogExpansion c hc)).2 hexpanded
