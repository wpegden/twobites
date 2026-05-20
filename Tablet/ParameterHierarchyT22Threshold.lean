import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT22Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT22Threshold :
    ∀ η : ℝ, 0 < η → η < (1 / 16 : ℝ) →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        2 * Real.log L * Real.sqrt L /
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) ∧
          Real.log L / L < (1 / 2 : ℝ) := by
-- BODY
  intro η hη_pos hη_lt_sixteen
  let r : ℝ := (1 / 4 : ℝ) - η
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith
  have hhalf_r_pos : 0 < r / 2 := by positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_quarter_half_power_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤
          (1 / 4 : ℝ) * Real.rpow (n : ℝ) (r / 2) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (r / 2)) :=
      isLittleO_log_rpow_atTop hhalf_r_pos
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.rpow (n : ℝ) (r / 2)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 4),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ Real.rpow (n : ℝ) (r / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hloglog_le_quarter_L_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (Real.log (n : ℝ)) ≤ (1 / 4 : ℝ) * Real.log (n : ℝ) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => Real.rpow x (1 : ℝ)) :=
      isLittleO_log_rpow_atTop zero_lt_one
    have hsmall_nat :
        (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[atTop]
          (fun n : ℕ => Real.rpow (Real.log (n : ℝ)) (1 : ℝ)) :=
      hsmall_real.comp_tendsto hlog_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 4),
      hlog_atTop.eventually_ge_atTop (1 : ℝ)] with n hbound hL_ge_one
    have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_nonneg hL_ge_one
    have hrpow_nonneg :
        0 ≤ Real.rpow (Real.log (n : ℝ)) (1 : ℝ) :=
      Real.rpow_nonneg (le_trans zero_le_one hL_ge_one) _
    rw [Real.norm_of_nonneg hloglog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa [Real.rpow_one] using hbound
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        2 * Real.log L * Real.sqrt L /
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) ∧
          Real.log L / L < (1 / 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hlog_le_quarter_half_power_eventually,
      hloglog_le_quarter_L_eventually] with n hn_ge_one hL_ge_one
        hL_le_quarter_half_power hloglog_le_quarter_L
    let L := Real.log (n : ℝ)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hL_ge_one_local : 1 ≤ L := by
      simpa [L] using hL_ge_one
    have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one_local
    have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one_local
    have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL_ge_one_local
    have hlogL_le_L : Real.log L ≤ L := Real.log_le_self hL_nonneg
    have hsqrtL_nonneg : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsqrtL_le_L : Real.sqrt L ≤ L := by
      have hL_le_L_sq : L ≤ L ^ 2 := by nlinarith
      calc
        Real.sqrt L ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt hL_le_L_sq
        _ = |L| := Real.sqrt_sq_eq_abs L
        _ = L := abs_of_nonneg hL_nonneg
    have hprod_le_L_sq : Real.log L * Real.sqrt L ≤ L ^ 2 := by
      calc
        Real.log L * Real.sqrt L ≤ L * L :=
          mul_le_mul hlogL_le_L hsqrtL_le_L hsqrtL_nonneg hL_nonneg
        _ = L ^ 2 := by ring
    have hhalf_power_sq :
        (Real.rpow (n : ℝ) (r / 2)) ^ 2 = Real.rpow (n : ℝ) r := by
      have hnat :
          (Real.rpow (n : ℝ) (r / 2)) ^ 2 =
            Real.rpow (Real.rpow (n : ℝ) (r / 2)) (2 : ℝ) := by
        exact (Real.rpow_natCast (Real.rpow (n : ℝ) (r / 2)) 2).symm
      calc
        (Real.rpow (n : ℝ) (r / 2)) ^ 2 =
            Real.rpow (Real.rpow (n : ℝ) (r / 2)) (2 : ℝ) := hnat
        _ = Real.rpow (n : ℝ) ((r / 2) * 2) := by
          exact (Real.rpow_mul hn_nonneg (r / 2) (2 : ℝ)).symm
        _ = Real.rpow (n : ℝ) r := by
          congr 1
          ring
    have hL_sq_le :
        L ^ 2 ≤ (1 / 16 : ℝ) * Real.rpow (n : ℝ) r := by
      have hpow :=
        pow_le_pow_left₀ hL_nonneg (by simpa [L] using hL_le_quarter_half_power) 2
      calc
        L ^ 2 ≤ ((1 / 4 : ℝ) * Real.rpow (n : ℝ) (r / 2)) ^ 2 := by
          simpa [one_div] using hpow
        _ = (1 / 16 : ℝ) * (Real.rpow (n : ℝ) (r / 2)) ^ 2 := by ring
        _ = (1 / 16 : ℝ) * Real.rpow (n : ℝ) r := by rw [hhalf_power_sq]
    have hpower_pos : 0 < Real.rpow (n : ℝ) r :=
      Real.rpow_pos_of_pos hn_pos _
    have hfirst_num_lt :
        2 * Real.log L * Real.sqrt L < (1 / 2 : ℝ) * Real.rpow (n : ℝ) r := by
      have htwo_prod_le :
          2 * Real.log L * Real.sqrt L ≤ 2 * L ^ 2 := by
        calc
          2 * Real.log L * Real.sqrt L =
              2 * (Real.log L * Real.sqrt L) := by ring
          _ ≤ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hprod_le_L_sq (by norm_num)
      have htwo_L_sq_le :
          2 * L ^ 2 ≤ (1 / 8 : ℝ) * Real.rpow (n : ℝ) r := by
        calc
          2 * L ^ 2 ≤ 2 * ((1 / 16 : ℝ) * Real.rpow (n : ℝ) r) :=
            mul_le_mul_of_nonneg_left hL_sq_le (by norm_num)
          _ = (1 / 8 : ℝ) * Real.rpow (n : ℝ) r := by ring
      have heighth_lt_half :
          (1 / 8 : ℝ) * Real.rpow (n : ℝ) r <
            (1 / 2 : ℝ) * Real.rpow (n : ℝ) r :=
        mul_lt_mul_of_pos_right (by norm_num : (1 / 8 : ℝ) < 1 / 2) hpower_pos
      exact lt_of_le_of_lt (le_trans htwo_prod_le htwo_L_sq_le) heighth_lt_half
    have hfirst :
        2 * Real.log L * Real.sqrt L /
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ (by simpa [r] using hpower_pos)]
      simpa [r, one_mul] using hfirst_num_lt
    have hsecond_num_lt : Real.log L < (1 / 2 : ℝ) * L := by
      have hquarter_lt_half :
          (1 / 4 : ℝ) * L < (1 / 2 : ℝ) * L :=
        mul_lt_mul_of_pos_right (by norm_num : (1 / 4 : ℝ) < 1 / 2) hL_pos
      exact lt_of_le_of_lt (by simpa [L] using hloglog_le_quarter_L) hquarter_lt_half
    have hsecond : Real.log L / L < (1 / 2 : ℝ) := by
      rw [div_lt_iff₀ hL_pos]
      simpa [one_mul] using hsecond_num_lt
    exact ⟨hfirst, hsecond⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
