import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT29Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT29Threshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        Real.exp
            (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
              Real.sqrt L * L) ≤ ε1 := by
-- BODY
  intro η ε1 hη_pos hε1_pos
  let c : ℝ := η * (1 + η) / 4
  have h_one_add_pos : 0 < 1 + η := by linarith
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hsqrt_atTop :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hn_atTop
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        Real.exp
            (-(η * (1 + η) / 4) * Real.sqrt (n : ℝ) *
              Real.sqrt L * L) ≤ ε1 := by
    filter_upwards [hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hsqrt_atTop.eventually_ge_atTop
        (max (0 : ℝ) ((-Real.log ε1) / c))] with n hL_ge_one hsqrt_ge
    let L := Real.log (n : ℝ)
    have hL_ge_one_local : (1 : ℝ) ≤ L := by
      simpa [L] using hL_ge_one
    have hsqrtL_ge_one : (1 : ℝ) ≤ Real.sqrt L := by
      simpa using Real.sqrt_le_sqrt hL_ge_one_local
    have hfactor_ge_one : (1 : ℝ) ≤ Real.sqrt L * L := by
      have hmul := mul_le_mul hsqrtL_ge_one hL_ge_one_local
        (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) hsqrtL_ge_one)
      simpa using hmul
    have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hsqrt_le_product :
        Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt L * L := by
      calc
        Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * 1 := by ring
        _ ≤ Real.sqrt (n : ℝ) * (Real.sqrt L * L) :=
          mul_le_mul_of_nonneg_left hfactor_ge_one hsqrt_nonneg
        _ = Real.sqrt (n : ℝ) * Real.sqrt L * L := by ring
    have hfloor :
        (-Real.log ε1) / c ≤ Real.sqrt (n : ℝ) :=
      le_trans (le_max_right (0 : ℝ) ((-Real.log ε1) / c)) hsqrt_ge
    have hlog_absorb :
        -Real.log ε1 ≤ c * (Real.sqrt (n : ℝ) * Real.sqrt L * L) := by
      have hscaled_floor :
          c * ((-Real.log ε1) / c) ≤ c * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hfloor (le_of_lt hc_pos)
      have hscaled_product :
          c * Real.sqrt (n : ℝ) ≤
            c * (Real.sqrt (n : ℝ) * Real.sqrt L * L) :=
        mul_le_mul_of_nonneg_left hsqrt_le_product (le_of_lt hc_pos)
      calc
        -Real.log ε1 = c * ((-Real.log ε1) / c) := by
          field_simp [ne_of_gt hc_pos]
        _ ≤ c * Real.sqrt (n : ℝ) := hscaled_floor
        _ ≤ c * (Real.sqrt (n : ℝ) * Real.sqrt L * L) := hscaled_product
    have harg_le_log :
        -(c * (Real.sqrt (n : ℝ) * Real.sqrt L * L)) ≤ Real.log ε1 := by
      linarith
    have harg_target :
        -(η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L ≤
          Real.log ε1 := by
      calc
        -(η * (1 + η) / 4) * Real.sqrt (n : ℝ) * Real.sqrt L * L =
            -(c * (Real.sqrt (n : ℝ) * Real.sqrt L * L)) := by
          dsimp [c]
          ring
        _ ≤ Real.log ε1 := harg_le_log
    exact (Real.le_log_iff_exp_le hε1_pos).1 harg_target
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
