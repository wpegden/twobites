import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT6LogThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT6LogThreshold :
    ∀ η : ℝ, 0 < η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) /
            ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) ≤
          η ^ 3 / 2 := by
-- BODY
  intro η hη
  let κ : ℝ := 1 + η
  let δ : ℝ := η ^ 3 * κ ^ 2 / 16
  have hκ_pos : 0 < κ := by dsimp [κ]; linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hquarter_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (4 : ℝ)⁻¹)).comp hn_atTop
  have hquarter_scale_eventually :
      ∀ᶠ n : ℕ in atTop, 1 ≤ δ * (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
    (hquarter_atTop.const_mul_atTop hδ_pos).eventually_ge_atTop (1 : ℝ)
  have hlog_le_half_quarter_eventually :
      ∀ᶠ n : ℕ in atTop,
        2 * Real.log (n : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((4 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (4 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((4 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : 0 < (1 / 2 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    nlinarith
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) /
            ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) ≤
          η ^ 3 / 2 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hn_atTop.eventually_ge_atTop (2 * κ),
      hquarter_scale_eventually,
      hlog_le_half_quarter_eventually] with n hn_ge_one hL_ge_one htwoκ_le_n
        hquarter_scale hlog_le_half_quarter
    let L := Real.log (n : ℝ)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hL_nonneg : 0 ≤ L := by
      exact le_trans zero_le_one (by simpa [L] using hL_ge_one)
    have hL_pos : 0 < L := by linarith [hL_ge_one]
    have hL_le_n : L ≤ (n : ℝ) := by
      dsimp [L]
      exact Real.log_le_self hn_nonneg
    have hnL_le_nsq : (n : ℝ) * L ≤ (n : ℝ) ^ 2 := by
      nlinarith
    have hsqrt_nL_le_n : Real.sqrt ((n : ℝ) * L) ≤ (n : ℝ) := by
      calc
        Real.sqrt ((n : ℝ) * L) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt hnL_le_nsq
        _ = |(n : ℝ)| := Real.sqrt_sq_eq_abs (n : ℝ)
        _ = (n : ℝ) := abs_of_nonneg hn_nonneg
    have hsqrt_nL_nonneg : 0 ≤ Real.sqrt ((n : ℝ) * L) := Real.sqrt_nonneg _
    have harg_le_nsq :
        2 * (1 + η) * Real.sqrt ((n : ℝ) * L) ≤ (n : ℝ) ^ 2 := by
      have hmul := mul_le_mul (by simpa [κ] using htwoκ_le_n) hsqrt_nL_le_n
        hsqrt_nL_nonneg hn_nonneg
      calc
        2 * (1 + η) * Real.sqrt ((n : ℝ) * L)
            = (2 * κ) * Real.sqrt ((n : ℝ) * L) := by dsimp [κ]
        _ ≤ (n : ℝ) * (n : ℝ) := hmul
        _ = (n : ℝ) ^ 2 := by ring
    have harg_pos : 0 < 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := by
      have hnL_pos : 0 < (n : ℝ) * L := mul_pos hn_pos hL_pos
      positivity
    have hlog_arg_le_twolog :
        Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
          2 * Real.log (n : ℝ) := by
      calc
        Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L))
            ≤ Real.log ((n : ℝ) ^ 2) :=
          Real.log_le_log harg_pos harg_le_nsq
        _ = 2 * Real.log (n : ℝ) := by
          rw [Real.log_pow]
          norm_num
    have hlog_arg_le_quarter :
        Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
          (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      le_trans hlog_arg_le_twolog hlog_le_half_quarter
    have hquarter_nonneg : 0 ≤ (n : ℝ) ^ ((4 : ℝ)⁻¹) :=
      Real.rpow_nonneg hn_nonneg _
    have hquarter_sq :
        ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2 = Real.sqrt (n : ℝ) := by
      calc
        ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2 =
            ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ (2 : ℝ) := by
          exact (Real.rpow_natCast ((n : ℝ) ^ ((4 : ℝ)⁻¹)) 2).symm
        _ = (n : ℝ) ^ (((4 : ℝ)⁻¹) * 2) := by
          rw [← Real.rpow_mul hn_nonneg]
        _ = (n : ℝ) ^ (1 / 2 : ℝ) := by norm_num
        _ = Real.sqrt (n : ℝ) := by rw [← Real.sqrt_eq_rpow]
    have hquarter_le_delta_sqrt :
        (n : ℝ) ^ ((4 : ℝ)⁻¹) ≤ δ * Real.sqrt (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hquarter_scale hquarter_nonneg
      calc
        (n : ℝ) ^ ((4 : ℝ)⁻¹) = 1 * (n : ℝ) ^ ((4 : ℝ)⁻¹) := by ring
        _ ≤ (δ * (n : ℝ) ^ ((4 : ℝ)⁻¹)) *
            (n : ℝ) ^ ((4 : ℝ)⁻¹) := hmul
        _ = δ * (((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 2) := by ring
        _ = δ * Real.sqrt (n : ℝ) := by rw [hquarter_sq]
    have hlog_arg_le_delta_sqrt :
        Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
          δ * Real.sqrt (n : ℝ) :=
      le_trans hlog_arg_le_quarter hquarter_le_delta_sqrt
    have hLpow_ge_one : (1 : ℝ) ≤ L ^ (3 / 2 : ℝ) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 / 2 : ℝ) := by rw [Real.one_rpow]
        _ ≤ L ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
            (by simpa [L] using hL_ge_one) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    have hden_pos :
        0 < (1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ) := by
      have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
      have hLpow_pos : 0 < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL_pos _
      positivity
    have hnum_le :
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
          (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) := by
      have hbase :
          8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L)) ≤
            (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) := by
        calc
          8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L))
              ≤ 8 * (δ * Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_arg_le_delta_sqrt (by norm_num)
          _ = (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) := by
            dsimp [δ, κ]
            ring
      have hfactor_nonneg : 0 ≤ (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) := by
        positivity
      calc
        8 * Real.log (2 * (1 + η) * Real.sqrt ((n : ℝ) * L))
            ≤ (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) := hbase
        _ = (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) * 1 := by ring
        _ ≤ (η ^ 3 / 2) * ((1 + η) ^ 2 * Real.sqrt (n : ℝ)) *
            L ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hLpow_ge_one hfactor_nonneg
        _ = (η ^ 3 / 2) *
            ((1 + η) ^ 2 * Real.sqrt (n : ℝ) * L ^ (3 / 2 : ℝ)) := by ring
    exact (div_le_iff₀ hden_pos).2 hnum_le
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩
