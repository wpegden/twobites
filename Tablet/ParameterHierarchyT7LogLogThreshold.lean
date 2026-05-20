import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT7LogLogThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT7LogLogThreshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        1 / ((1 + η) * Real.log L) ≤ ε1 := by
-- BODY
  intro η ε1 hη hε1
  have hκ_pos : 0 < 1 + η := by linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hloglog_atTop :
      Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_atTop
  have h_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        1 / ((1 + η) * Real.log L) ≤ ε1 := by
    filter_upwards [hloglog_atTop.eventually_ge_atTop (1 / ((1 + η) * ε1))]
      with n hloglog_ge
    let L := Real.log (n : ℝ)
    have hden_lower :
        1 / ε1 ≤ (1 + η) * Real.log L := by
      calc
        1 / ε1 = (1 + η) * (1 / ((1 + η) * ε1)) := by
          field_simp [hκ_pos.ne', hε1.ne']
        _ ≤ (1 + η) * Real.log L :=
          mul_le_mul_of_nonneg_left (by simpa [L] using hloglog_ge) (le_of_lt hκ_pos)
    have hleft_pos : 0 < 1 / ε1 := by positivity
    have hinv_le : ((1 + η) * Real.log L)⁻¹ ≤ (1 / ε1)⁻¹ :=
      inv_anti₀ hleft_pos hden_lower
    have hinv_eq : (1 / ε1)⁻¹ = ε1 := by field_simp [hε1.ne']
    simpa [one_div, hinv_eq] using hinv_le
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp h_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
