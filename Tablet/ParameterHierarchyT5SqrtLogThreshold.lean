import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT5SqrtLogThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT5SqrtLogThreshold :
    ∀ ε1 : ℝ, 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        1 / Real.sqrt L ≤ ε1 / 2 := by
-- BODY
  intro ε1 hε1
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have h_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        1 / Real.sqrt L ≤ ε1 / 2 := by
    filter_upwards [hlog_atTop.eventually_ge_atTop ((2 / ε1) ^ 2)] with n hL_ge
    let L := Real.log (n : ℝ)
    have htwo_div_pos : 0 < 2 / ε1 := by positivity
    have htwo_div_nonneg : 0 ≤ 2 / ε1 := le_of_lt htwo_div_pos
    have hL_nonneg : 0 ≤ L := by
      exact le_trans (sq_nonneg (2 / ε1)) (by simpa [L] using hL_ge)
    have hsqrt_ge : 2 / ε1 ≤ Real.sqrt L := by
      exact (Real.le_sqrt htwo_div_nonneg hL_nonneg).2 (by simpa [L] using hL_ge)
    have hsqrt_pos : 0 < Real.sqrt L := lt_of_lt_of_le htwo_div_pos hsqrt_ge
    have h_inv_le : (Real.sqrt L)⁻¹ ≤ (2 / ε1)⁻¹ :=
      inv_anti₀ htwo_div_pos hsqrt_ge
    have h_inv_eq : (2 / ε1)⁻¹ = ε1 / 2 := by field_simp [hε1.ne']
    simpa [one_div, h_inv_eq] using h_inv_le
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp h_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
