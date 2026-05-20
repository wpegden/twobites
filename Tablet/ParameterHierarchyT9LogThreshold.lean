import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT9LogThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT9LogThreshold :
    ∀ ε1 : ℝ, 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L / L ^ 2 ≤ ε1 / 10 := by
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
        2 * Real.log L / L ^ 2 ≤ ε1 / 10 := by
    filter_upwards [hlog_atTop.eventually_ge_atTop (max (1 : ℝ) (20 / ε1))]
      with n hL_ge
    let L := Real.log (n : ℝ)
    have hL_ge_one : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) (by simpa [L] using hL_ge)
    have hL_ge_twenty : 20 / ε1 ≤ L :=
      le_trans (le_max_right _ _) (by simpa [L] using hL_ge)
    have hL_nonneg : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one
    have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one
    have hlogL_le_L : Real.log L ≤ L := Real.log_le_self hL_nonneg
    have hfirst :
        2 * Real.log L / L ^ 2 ≤ 2 / L := by
      have hnum_le : 2 * Real.log L ≤ 2 * L :=
        mul_le_mul_of_nonneg_left hlogL_le_L (by norm_num)
      calc
        2 * Real.log L / L ^ 2 ≤ 2 * L / L ^ 2 :=
          div_le_div_of_nonneg_right hnum_le (sq_nonneg L)
        _ = 2 / L := by field_simp [hL_pos.ne']
    have hsecond : 2 / L ≤ ε1 / 10 := by
      have hmul : 20 ≤ ε1 * L := by
        have := mul_le_mul_of_nonneg_left hL_ge_twenty (le_of_lt hε1)
        field_simp [hε1.ne'] at this
        linarith
      field_simp [hL_pos.ne', hε1.ne']
      nlinarith
    exact le_trans hfirst hsecond
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp h_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩

