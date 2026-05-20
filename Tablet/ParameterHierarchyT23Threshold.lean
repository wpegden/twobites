import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT23Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT23Threshold :
    ∀ η : ℝ, 0 < η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 := by
-- BODY
  intro η hη_pos
  have hthird_pos : 0 < η / 3 := by positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_le_eighth_third_power_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤
          (1 / 8 : ℝ) * Real.rpow (n : ℝ) (η / 3) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (η / 3)) :=
      isLittleO_log_rpow_atTop hthird_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) (η / 3)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 8),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (η / 3) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        200 * L ^ 3 / Real.rpow (n : ℝ) η ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_le_eighth_third_power_eventually] with n hn_ge_one hL_le
    let L := Real.log (n : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_nonneg : 0 ≤ L := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hthird_power_cube :
        (Real.rpow (n : ℝ) (η / 3)) ^ 3 = Real.rpow (n : ℝ) η := by
      have hnat :
          (Real.rpow (n : ℝ) (η / 3)) ^ 3 =
            Real.rpow (Real.rpow (n : ℝ) (η / 3)) (3 : ℝ) := by
        exact (Real.rpow_natCast (Real.rpow (n : ℝ) (η / 3)) 3).symm
      calc
        (Real.rpow (n : ℝ) (η / 3)) ^ 3 =
            Real.rpow (Real.rpow (n : ℝ) (η / 3)) (3 : ℝ) := hnat
        _ = Real.rpow (n : ℝ) ((η / 3) * 3) := by
          exact (Real.rpow_mul hn_nonneg (η / 3) (3 : ℝ)).symm
        _ = Real.rpow (n : ℝ) η := by
          congr 1
          ring
    have hL_cube_le :
        L ^ 3 ≤ (1 / 512 : ℝ) * Real.rpow (n : ℝ) η := by
      have hpow :=
        pow_le_pow_left₀ hL_nonneg (by simpa [L] using hL_le) 3
      calc
        L ^ 3 ≤ ((1 / 8 : ℝ) * Real.rpow (n : ℝ) (η / 3)) ^ 3 := by
          simpa [one_div] using hpow
        _ = (1 / 512 : ℝ) * (Real.rpow (n : ℝ) (η / 3)) ^ 3 := by ring
        _ = (1 / 512 : ℝ) * Real.rpow (n : ℝ) η := by rw [hthird_power_cube]
    have hpower_pos : 0 < Real.rpow (n : ℝ) η :=
      Real.rpow_pos_of_pos hn_pos _
    have hnum_le_power :
        200 * L ^ 3 ≤ Real.rpow (n : ℝ) η := by
      calc
        200 * L ^ 3 ≤ 200 * ((1 / 512 : ℝ) * Real.rpow (n : ℝ) η) :=
          mul_le_mul_of_nonneg_left hL_cube_le (by norm_num)
        _ = (25 / 64 : ℝ) * Real.rpow (n : ℝ) η := by ring
        _ ≤ 1 * Real.rpow (n : ℝ) η :=
          mul_le_mul_of_nonneg_right (by norm_num : (25 / 64 : ℝ) ≤ 1)
            (le_of_lt hpower_pos)
        _ = Real.rpow (n : ℝ) η := by ring
    rw [div_le_iff₀ hpower_pos]
    simpa [one_mul] using hnum_le_power
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
