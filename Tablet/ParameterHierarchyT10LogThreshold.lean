import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT10LogThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT10LogThreshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L / ((1 + η) * L ^ 4) ≤ ε1 := by
-- BODY
  intro η ε1 hη hε1
  have hκ_pos : 0 < 1 + η := by linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have h_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 * Real.log L / ((1 + η) * L ^ 4) ≤ ε1 := by
    filter_upwards [hlog_atTop.eventually_ge_atTop (max (1 : ℝ) (2 / ((1 + η) * ε1)))]
      with n hL_ge
    let L := Real.log (n : ℝ)
    have hL_ge_one : (1 : ℝ) ≤ L := le_trans (le_max_left _ _) (by simpa [L] using hL_ge)
    have hL_ge_target : 2 / ((1 + η) * ε1) ≤ L :=
      le_trans (le_max_right _ _) (by simpa [L] using hL_ge)
    have hL_nonneg : 0 ≤ L := le_trans (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one
    have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one
    have hlogL_le_L : Real.log L ≤ L := Real.log_le_self hL_nonneg
    have hsecond : 2 / ((1 + η) * L) ≤ ε1 := by
      have hmul : 2 ≤ (1 + η) * ε1 * L := by
        have := mul_le_mul_of_nonneg_left hL_ge_target (by positivity : 0 ≤ (1 + η) * ε1)
        field_simp [hκ_pos.ne', hε1.ne'] at this
        linarith
      field_simp [hκ_pos.ne', hε1.ne', hL_pos.ne']
      nlinarith
    calc
      2 * Real.log L / ((1 + η) * L ^ 4) ≤ 2 / ((1 + η) * L) := by
        have hnum_le : 2 * Real.log L ≤ 2 * L :=
          mul_le_mul_of_nonneg_left hlogL_le_L (by norm_num)
        have hden4_pos : 0 < (1 + η) * L ^ 4 := by positivity
        calc
          2 * Real.log L / ((1 + η) * L ^ 4) ≤ 2 * L / ((1 + η) * L ^ 4) :=
            div_le_div_of_nonneg_right hnum_le (le_of_lt hden4_pos)
          _ = 2 / ((1 + η) * L ^ 3) := by field_simp [hκ_pos.ne', hL_pos.ne']
          _ ≤ 2 / ((1 + η) * L) := by
            have hden_pos : 0 < (1 + η) * L := mul_pos hκ_pos hL_pos
            have hden3_pos : 0 < (1 + η) * L ^ 3 := by positivity
            have hL_le_L3 : L ≤ L ^ 3 := by
              have hL2_ge_one : (1 : ℝ) ≤ L ^ 2 := by
                nlinarith [sq_nonneg (L - 1), hL_ge_one]
              calc
                L = L * 1 := by ring
                _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_left hL2_ge_one hL_nonneg
                _ = L ^ 3 := by ring
            have hden_le : (1 + η) * L ≤ (1 + η) * L ^ 3 :=
              mul_le_mul_of_nonneg_left hL_le_L3 (le_of_lt hκ_pos)
            exact div_le_div_of_nonneg_left (by norm_num) hden_pos hden_le
      _ ≤ ε1 := hsecond
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp h_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩

