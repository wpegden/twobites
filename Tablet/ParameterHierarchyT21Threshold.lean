import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT21Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT21Threshold :
    ∀ η : ℝ, 0 < η → η < (1 / 16 : ℝ) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        Real.log L /
            (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L) < 1 := by
-- BODY
  intro η hη_pos hη_lt_sixteen
  have hr_pos : 0 < (1 / 4 : ℝ) - η := by
    linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_half_power_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤
          (1 / 2 : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x ((1 / 4 : ℝ) - η)) :=
      isLittleO_log_rpow_atTop hr_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg :
        0 ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        Real.log L /
            (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L) < 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hlog_le_half_power_eventually] with n hn_ge_one hL_ge_one hL_le_half_power
    let L := Real.log (n : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_ge_one_local : 1 ≤ L := by
      simpa [L] using hL_ge_one
    have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one_local
    have hlogL_le_L : Real.log L ≤ L := Real.log_le_self hL_nonneg
    have hpower_pos :
        0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) :=
      Real.rpow_pos_of_pos hn_pos _
    have hsqrtL_ge_one : 1 ≤ Real.sqrt L := by
      simpa using Real.sqrt_le_sqrt hL_ge_one_local
    have hnum_lt_den :
        Real.log L <
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L := by
      calc
        Real.log L ≤ L := hlogL_le_L
        _ ≤ (1 / 2 : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) := by
          simpa [L] using hL_le_half_power
        _ < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) := by
          linarith
        _ ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L := by
          calc
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
                Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * 1 := by ring
            _ ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L :=
              mul_le_mul_of_nonneg_left hsqrtL_ge_one (le_of_lt hpower_pos)
    have hden_pos :
        0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) * Real.sqrt L :=
      mul_pos hpower_pos (lt_of_lt_of_le zero_lt_one hsqrtL_ge_one)
    rw [div_lt_iff₀ hden_pos]
    simpa [L, one_mul] using hnum_lt_den
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
