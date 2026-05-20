import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT12Threshold]

open Filter
open scoped Topology

theorem ParameterHierarchyT12Threshold :
    ∀ η ε1 : ℝ, 0 < η → 0 < ε1 → ε1 ≤ 1 →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 /
            (ε1 * ((1 + η) ^ 2 * (n : ℝ))) ≤ 1 := by
-- BODY
  intro η ε1 hη hε1 hε1_le_one
  let κ : ℝ := 1 + η
  let c : ℝ := ε1 * (100000 * κ)⁻¹
  have hκ_pos : 0 < κ := by dsimp [κ]; linarith
  have hκ_ge_one : 1 ≤ κ := by dsimp [κ]; linarith
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hconst : 400000 * (5 * κ) ^ 2 * c ^ 7 ≤ ε1 * κ ^ 2 := by
    have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
    have hε1_nonneg : 0 ≤ ε1 := le_of_lt hε1
    have hκ7_ge_one : (1 : ℝ) ≤ κ ^ 7 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hκ_ge_one 7
    have hε1_six_le_one : ε1 ^ 6 ≤ 1 := by
      simpa using pow_le_pow_left₀ hε1_nonneg hε1_le_one 6
    have hε1_seven_le : ε1 ^ 7 ≤ ε1 := by
      calc
        ε1 ^ 7 = ε1 * ε1 ^ 6 := by ring
        _ ≤ ε1 * 1 := mul_le_mul_of_nonneg_left hε1_six_le_one hε1_nonneg
        _ = ε1 := by ring
    have hden_pos : 0 < (100000 * κ) ^ 7 := by positivity
    dsimp [c]
    rw [show (ε1 * (100000 * κ)⁻¹) ^ 7 = ε1 ^ 7 * ((100000 * κ) ^ 7)⁻¹ by
      rw [mul_pow, inv_pow]]
    rw [← div_eq_mul_inv]
    rw [show
        400000 * (5 * κ) ^ 2 * (ε1 ^ 7 / (100000 * κ) ^ 7) =
          (400000 * (5 * κ) ^ 2 * ε1 ^ 7) / (100000 * κ) ^ 7 by ring]
    rw [div_le_iff₀ hden_pos]
    rw [mul_pow (100000 : ℝ) κ 7, mul_pow (5 : ℝ) κ 2]
    norm_num
    calc
      400000 * (25 * κ ^ 2) * ε1 ^ 7 ≤ 400000 * (25 * κ ^ 2) * ε1 :=
        mul_le_mul_of_nonneg_left hε1_seven_le (by positivity)
      _ ≤ ε1 * κ ^ 2 * (100000000000000000000000000000000000 * κ ^ 7) := by
        have hκ2_le_κ9 : κ ^ 2 ≤ κ ^ 2 * κ ^ 7 := by
          calc
            κ ^ 2 = κ ^ 2 * 1 := by ring
            _ ≤ κ ^ 2 * κ ^ 7 :=
              mul_le_mul_of_nonneg_left hκ7_ge_one (sq_nonneg κ)
        have hcoef :
            400000 * (25 * κ ^ 2) ≤
              100000000000000000000000000000000000 * (κ ^ 2 * κ ^ 7) := by
          nlinarith
        calc
          400000 * (25 * κ ^ 2) * ε1 =
              ε1 * (400000 * (25 * κ ^ 2)) := by ring
          _ ≤ ε1 *
              (100000000000000000000000000000000000 * (κ ^ 2 * κ ^ 7)) :=
            mul_le_mul_of_nonneg_left hcoef hε1_nonneg
          _ = ε1 * κ ^ 2 *
              (100000000000000000000000000000000000 * κ ^ 7) := by ring
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_c_tenth_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ c * (n : ℝ) ^ ((10 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((10 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : 0 < (10 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((10 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hc_pos, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((10 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  have hmain_eventually :
      ∀ᶠ n : ℕ in atTop,
        let L := Real.log (n : ℝ)
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 /
            (ε1 * ((1 + η) ^ 2 * (n : ℝ))) ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ),
      hlog_le_c_tenth_eventually] with n hn_ge_one hL_ge_one hL_le_c_tenth
    let L := Real.log (n : ℝ)
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
    have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
    have hL_nonneg : 0 ≤ L := by
      exact le_trans zero_le_one (by simpa [L] using hL_ge_one)
    have hL_pos : 0 < L := by linarith [hL_ge_one]
    have hlogL_nonneg : 0 ≤ Real.log L := Real.log_nonneg (by simpa [L] using hL_ge_one)
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
    have hL_le_c_tenth : L ≤ c * (n : ℝ) ^ ((10 : ℝ)⁻¹) := by
      simpa [L] using hL_le_c_tenth
    have hL7_le :
        L ^ 7 ≤ c ^ 7 * (n : ℝ) := by
      have hpow :=
        pow_le_pow_left₀ hL_nonneg hL_le_c_tenth 7
      have hrpow7 :
          ((n : ℝ) ^ ((10 : ℝ)⁻¹)) ^ 7 = (n : ℝ) ^ (7 / 10 : ℝ) := by
        calc
          ((n : ℝ) ^ ((10 : ℝ)⁻¹)) ^ 7 =
              ((n : ℝ) ^ ((10 : ℝ)⁻¹)) ^ (7 : ℝ) := by
            exact (Real.rpow_natCast ((n : ℝ) ^ ((10 : ℝ)⁻¹)) 7).symm
          _ = (n : ℝ) ^ (((10 : ℝ)⁻¹) * 7) := by
            rw [← Real.rpow_mul hn_nonneg]
          _ = (n : ℝ) ^ (7 / 10 : ℝ) := by norm_num
      have hrpow_le_n : (n : ℝ) ^ (7 / 10 : ℝ) ≤ (n : ℝ) := by
        simpa [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hn_ge_one_real
            (by norm_num : (7 / 10 : ℝ) ≤ 1)
      calc
        L ^ 7 ≤ (c * (n : ℝ) ^ ((10 : ℝ)⁻¹)) ^ 7 := hpow
        _ = c ^ 7 * ((n : ℝ) ^ ((10 : ℝ)⁻¹)) ^ 7 := by ring
        _ = c ^ 7 * ((n : ℝ) ^ (7 / 10 : ℝ)) := by rw [hrpow7]
        _ ≤ c ^ 7 * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hrpow_le_n (by positivity)
    have hpoly_le :
        (Real.log L) ^ 2 * L ^ 5 ≤ c ^ 7 * (n : ℝ) :=
      le_trans hlogL2L5_le_L7 hL7_le
    have hnum_le_den :
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5 ≤
          ε1 * ((1 + η) ^ 2 * (n : ℝ)) := by
      calc
        400000 * (5 * (1 + η)) ^ 2 * (Real.log L) ^ 2 * L ^ 5
            = 400000 * (5 * κ) ^ 2 * ((Real.log L) ^ 2 * L ^ 5) := by
          dsimp [κ]
          ring
        _ ≤ 400000 * (5 * κ) ^ 2 * (c ^ 7 * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hpoly_le (by positivity)
        _ = (400000 * (5 * κ) ^ 2 * c ^ 7) * (n : ℝ) := by ring
        _ ≤ (ε1 * κ ^ 2) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hconst hn_nonneg
        _ = ε1 * ((1 + η) ^ 2 * (n : ℝ)) := by dsimp [κ]; ring
    have hden_pos :
        0 < ε1 * ((1 + η) ^ 2 * (n : ℝ)) := by
      dsimp [κ] at hκ_pos
      positivity
    exact (div_le_one hden_pos).2 hnum_le_den
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hmain_eventually
  exact ⟨n0, fun n hn => hn0 n (le_of_lt hn)⟩

