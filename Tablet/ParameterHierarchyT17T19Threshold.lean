import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT17T19Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT17T19Threshold :
    ∀ η ε2 : ℝ, 0 < η → 0 < ε2 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
          200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
              Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
            400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
                Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 := by
-- BODY
  intro η ε2 hη hε2
  let C : ℝ := 400 * (5 * (1 + η))
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  have hC_nonneg : 0 ≤ C := le_of_lt hC_pos
  have hδ_pos : 0 < ε2 / (100 * C) := by
    positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_sixteenth_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ (n : ℝ) ^ ((16 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((16 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (16 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((16 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((16 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hnegative_power_small_eventually :
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ (-(1 / 16 : ℝ)) ≤ ε2 / (100 * C) := by
    have hlim_real :
        Tendsto (fun x : ℝ => x ^ (-(1 / 16 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 16)
    have hlim_nat :
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 16 : ℝ))) atTop (𝓝 0) :=
      hlim_real.comp hn_atTop
    filter_upwards [hlim_nat.eventually (Iio_mem_nhds hδ_pos)] with n hn
    exact le_of_lt hn
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
          200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
              Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 ∧
            400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
                Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hlog_le_sixteenth_eventually,
      hnegative_power_small_eventually] with n hn_ge_one hL_ge_one_raw
        hL_le_sixteenth_raw hn_negative_small
    let L := Real.log (n : ℝ)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_ge_one : 1 ≤ L := by
      simpa [L] using hL_ge_one_raw
    have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge_one
    have hL_pos : 0 < L := by linarith
    have hL_le_sixteenth : L ≤ (n : ℝ) ^ ((16 : ℝ)⁻¹) := by
      simpa [L] using hL_le_sixteenth_raw
    have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg hL_ge_one
    have hlogL_le_L : Real.log L ≤ L := Real.log_le_self hL_nonneg
    have hlogL_sq_le_L_sq :
        (Real.log L) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hlogL_nonneg hlogL_le_L 2
    have hlogL2L5_le_L7 :
        (Real.log L) ^ 2 * L ^ 5 ≤ L ^ 7 := by
      have hmul :=
        mul_le_mul_of_nonneg_right hlogL_sq_le_L_sq (by positivity : 0 ≤ L ^ 5)
      calc
        (Real.log L) ^ 2 * L ^ 5 ≤ L ^ 2 * L ^ 5 := hmul
        _ = L ^ 7 := by ring
    have hL7_le_rpow :
        L ^ 7 ≤ (n : ℝ) ^ (7 / 16 : ℝ) := by
      have hpow :=
        pow_le_pow_left₀ hL_nonneg hL_le_sixteenth 7
      have hrpow7 :
          ((n : ℝ) ^ ((16 : ℝ)⁻¹)) ^ 7 = (n : ℝ) ^ (7 / 16 : ℝ) := by
        calc
          ((n : ℝ) ^ ((16 : ℝ)⁻¹)) ^ 7 =
              ((n : ℝ) ^ ((16 : ℝ)⁻¹)) ^ (7 : ℝ) := by
            exact (Real.rpow_natCast ((n : ℝ) ^ ((16 : ℝ)⁻¹)) 7).symm
          _ = (n : ℝ) ^ (((16 : ℝ)⁻¹) * 7) := by
            rw [← Real.rpow_mul hn_nonneg]
          _ = (n : ℝ) ^ (7 / 16 : ℝ) := by norm_num
      calc
        L ^ 7 ≤ ((n : ℝ) ^ ((16 : ℝ)⁻¹)) ^ 7 := hpow
        _ = (n : ℝ) ^ (7 / 16 : ℝ) := hrpow7
    have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
    have hL7_div_sqrtn_le :
        L ^ 7 / Real.sqrt (n : ℝ) ≤ (n : ℝ) ^ (-(1 / 16 : ℝ)) := by
      calc
        L ^ 7 / Real.sqrt (n : ℝ) ≤
            (n : ℝ) ^ (7 / 16 : ℝ) / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_right hL7_le_rpow (le_of_lt hsqrtn_pos)
        _ = (n : ℝ) ^ (-(1 / 16 : ℝ)) := by
          rw [Real.sqrt_eq_rpow]
          rw [div_eq_mul_inv]
          rw [← Real.rpow_neg hn_nonneg]
          rw [← Real.rpow_add hn_pos]
          norm_num
    have hC_L7_div_sqrtn_le :
        C * (L ^ 7 / Real.sqrt (n : ℝ)) ≤ ε2 / 100 := by
      have hle_small :
          L ^ 7 / Real.sqrt (n : ℝ) ≤ ε2 / (100 * C) :=
        le_trans hL7_div_sqrtn_le hn_negative_small
      have hmul := mul_le_mul_of_nonneg_left hle_small hC_nonneg
      calc
        C * (L ^ 7 / Real.sqrt (n : ℝ)) ≤ C * (ε2 / (100 * C)) := hmul
        _ = ε2 / 100 := by
          field_simp [ne_of_gt hC_pos]
    have hn_le_nL : (n : ℝ) ≤ (n : ℝ) * L := by
      calc
        (n : ℝ) = (n : ℝ) * 1 := by ring
        _ ≤ (n : ℝ) * L :=
          mul_le_mul_of_nonneg_left hL_ge_one hn_nonneg
    have hsqrtn_le_sqrtnL :
        Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_le_sqrt hn_le_nL
    have hnL_pos : 0 < (n : ℝ) * L := mul_pos hn_pos hL_pos
    have hsqrtnL_pos : 0 < Real.sqrt ((n : ℝ) * L) :=
      Real.sqrt_pos.mpr hnL_pos
    have h400 :
        400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 := by
      change C * (Real.log L) ^ 2 * L ^ 5 / Real.sqrt ((n : ℝ) * L) ≤
        ε2 / 100
      have hnum_le : C * (Real.log L) ^ 2 * L ^ 5 ≤ C * L ^ 7 := by
        calc
          C * (Real.log L) ^ 2 * L ^ 5 =
              C * ((Real.log L) ^ 2 * L ^ 5) := by ring
          _ ≤ C * L ^ 7 :=
            mul_le_mul_of_nonneg_left hlogL2L5_le_L7 hC_nonneg
      calc
        C * (Real.log L) ^ 2 * L ^ 5 / Real.sqrt ((n : ℝ) * L) ≤
            C * L ^ 7 / Real.sqrt ((n : ℝ) * L) :=
          div_le_div_of_nonneg_right hnum_le (le_of_lt hsqrtnL_pos)
        _ ≤ C * L ^ 7 / Real.sqrt (n : ℝ) :=
          div_le_div_of_nonneg_left (by positivity : 0 ≤ C * L ^ 7)
            hsqrtn_pos hsqrtn_le_sqrtnL
        _ = C * (L ^ 7 / Real.sqrt (n : ℝ)) := by ring
        _ ≤ ε2 / 100 := hC_L7_div_sqrtn_le
    have hL2_ge_one : 1 ≤ L ^ 2 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hL_ge_one 2
    have hL3_le_L5 : L ^ 3 ≤ L ^ 5 := by
      calc
        L ^ 3 = L ^ 3 * 1 := by ring
        _ ≤ L ^ 3 * L ^ 2 :=
          mul_le_mul_of_nonneg_left hL2_ge_one (by positivity : 0 ≤ L ^ 3)
        _ = L ^ 5 := by ring
    have hfactor_nonneg : 0 ≤ (5 * (1 + η)) * (Real.log L) ^ 2 := by
      positivity
    have h100L3_le_400L5 : 100 * L ^ 3 ≤ 400 * L ^ 5 := by
      calc
        100 * L ^ 3 ≤ 100 * L ^ 5 :=
          mul_le_mul_of_nonneg_left hL3_le_L5 (by norm_num : (0 : ℝ) ≤ 100)
        _ ≤ 400 * L ^ 5 :=
          mul_le_mul_of_nonneg_right (by norm_num : (100 : ℝ) ≤ 400)
            (by positivity : 0 ≤ L ^ 5)
    have h200L3_le_400L5 : 200 * L ^ 3 ≤ 400 * L ^ 5 := by
      calc
        200 * L ^ 3 ≤ 200 * L ^ 5 :=
          mul_le_mul_of_nonneg_left hL3_le_L5 (by norm_num : (0 : ℝ) ≤ 200)
        _ ≤ 400 * L ^ 5 :=
          mul_le_mul_of_nonneg_right (by norm_num : (200 : ℝ) ≤ 400)
            (by positivity : 0 ≤ L ^ 5)
    have h100_num_le :
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 ≤
          400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 := by
      calc
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 =
            ((5 * (1 + η)) * (Real.log L) ^ 2) * (100 * L ^ 3) := by ring
        _ ≤ ((5 * (1 + η)) * (Real.log L) ^ 2) * (400 * L ^ 5) :=
          mul_le_mul_of_nonneg_left h100L3_le_400L5 hfactor_nonneg
        _ = 400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 := by ring
    have h200_num_le :
        200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 ≤
          400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 := by
      calc
        200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 =
            ((5 * (1 + η)) * (Real.log L) ^ 2) * (200 * L ^ 3) := by ring
        _ ≤ ((5 * (1 + η)) * (Real.log L) ^ 2) * (400 * L ^ 5) :=
          mul_le_mul_of_nonneg_left h200L3_le_400L5 hfactor_nonneg
        _ = 400 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 5 := by ring
    have h100 :
        100 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 :=
      le_trans (div_le_div_of_nonneg_right h100_num_le (le_of_lt hsqrtnL_pos)) h400
    have h200 :
        200 * (5 * (1 + η)) * (Real.log L) ^ 2 * L ^ 3 /
            Real.sqrt ((n : ℝ) * L) ≤ ε2 / 100 :=
      le_trans (div_le_div_of_nonneg_right h200_num_le (le_of_lt hsqrtnL_pos)) h400
    exact ⟨h100, h200, h400⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
