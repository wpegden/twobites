import Tablet.RamseyScale
import Tablet.RamseyScalePositiveCoefficientLogRatio
import Tablet.RamseyScalePositiveCoefficientTendstoAtTop

-- [TABLET NODE: RamseyScaleConversion]

theorem RamseyScaleConversion :
    ∀ η : ℝ, 0 < η → η < (1 : ℝ) / 2 →
      Filter.Tendsto (fun k : ℕ => ((1 : ℝ) / 2 - η) * RamseyScale k)
        Filter.atTop Filter.atTop ∧
      Filter.Tendsto
        (fun k : ℕ =>
          Real.log (((1 : ℝ) / 2 - η) * RamseyScale k) /
            Real.log (k : ℝ))
        Filter.atTop (nhds (2 : ℝ)) := by
-- BODY
  intro η hη hη_lt
  have hc : 0 < (1 : ℝ) / 2 - η := by
    linarith
  exact
    ⟨RamseyScalePositiveCoefficientTendstoAtTop ((1 : ℝ) / 2 - η) hc,
      RamseyScalePositiveCoefficientLogRatio ((1 : ℝ) / 2 - η) hc⟩
