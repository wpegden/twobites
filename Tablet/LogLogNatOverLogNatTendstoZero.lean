import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Tablet.Preamble

-- [TABLET NODE: LogLogNatOverLogNatTendstoZero]

theorem LogLogNatOverLogNatTendstoZero :
    Filter.Tendsto
      (fun k : ℕ => Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))
      Filter.atTop (nhds (0 : ℝ)) := by
-- BODY
  have hreal :
      Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) zero_lt_one).tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
