import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch

open Filter
open scoped Topology

-- [TABLET NODE: TwoBiteNaturalReducedVertexRatioEventually]

theorem TwoBiteNaturalReducedVertexRatioEventually :
    ∀ m : ℕ → ℕ,
      (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        ∀ᶠ n : ℕ in Filter.atTop,
          (n : ℝ) ≤ 2 * (Real.log (n : ℝ)) ^ 2 * (m n : ℝ) := by
-- BODY
  intro m hm
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hlog_le_quarter :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤
          (1 / 2 : ℝ) * (n : ℝ) ^ ((4 : ℝ)⁻¹) := by
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
    rw [Real.norm_of_nonneg hlog_nonneg,
      Real.norm_of_nonneg hrpow_nonneg] at hbound
    simpa using hbound
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlog_atTop.eventually_ge_atTop (1 : ℝ), hlog_le_quarter]
    with n hn_ge_one hL_ge_one hL_le
  let L : ℝ := Real.log (n : ℝ)
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
  have hL_nonneg : 0 ≤ L := by
    exact le_trans zero_le_one (by simpa [L] using hL_ge_one)
  have hL_pos : 0 < L := by linarith [hL_ge_one]
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hn_rpow4 :
      ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 = (n : ℝ) := by
    calc
      ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 =
          ((n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ (4 : ℝ) := by
        exact (Real.rpow_natCast ((n : ℝ) ^ ((4 : ℝ)⁻¹)) 4).symm
      _ = (n : ℝ) ^ (((4 : ℝ)⁻¹) * 4) := by
        rw [← Real.rpow_mul hn_nonneg]
      _ = (n : ℝ) := by norm_num
  have hL4_le :
      L ^ 4 ≤ ((1 / 2 : ℝ) * (n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 :=
    pow_le_pow_left₀ hL_nonneg hL_le 4
  have hfourL4_le_n : 4 * L ^ 4 ≤ (n : ℝ) := by
    calc
      4 * L ^ 4 ≤
          4 * ((1 / 2 : ℝ) * (n : ℝ) ^ ((4 : ℝ)⁻¹)) ^ 4 := by
        nlinarith
      _ = (1 / 4 : ℝ) * (n : ℝ) := by
        rw [mul_pow, hn_rpow4]
        ring
      _ ≤ (n : ℝ) := by nlinarith
  have hx_ge_two : 2 ≤ (n : ℝ) / L ^ 2 := by
    have hL2_pos : 0 < L ^ 2 := sq_pos_of_ne_zero hL_ne
    rw [le_div_iff₀ hL2_pos]
    have htwoL2_le_fourL4 : 2 * L ^ 2 ≤ 4 * L ^ 4 := by
      have hL2_ge_one : 1 ≤ L ^ 2 := by nlinarith [hL_ge_one]
      nlinarith [sq_nonneg (L ^ 2)]
    nlinarith
  have hfloor_lower :
      (n : ℝ) / (2 * L ^ 2) ≤
        (Nat.floor ((n : ℝ) / L ^ 2) : ℝ) := by
    have hsub := Nat.sub_one_lt_floor ((n : ℝ) / L ^ 2)
    have hx_half : ((n : ℝ) / L ^ 2) / 2 ≤
        (n : ℝ) / L ^ 2 - 1 := by
      linarith
    have hhalf_eq :
        (n : ℝ) / (2 * L ^ 2) = ((n : ℝ) / L ^ 2) / 2 := by
      field_simp [hL_ne]
    rw [hhalf_eq]
    linarith
  have hm_cast :
      (m n : ℝ) = (Nat.floor ((n : ℝ) / L ^ 2) : ℝ) := by
    rw [hm n, TwoBiteNaturalReducedVertexCount,
      TwoBiteReducedVertexCount, TwoBiteStretch]
  have hlower : (n : ℝ) / (2 * L ^ 2) ≤ (m n : ℝ) := by
    rw [hm_cast]
    exact hfloor_lower
  have hden_pos : 0 < 2 * L ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlower hden_pos.le
  have hcancel : 2 * L ^ 2 * ((n : ℝ) / (2 * L ^ 2)) = (n : ℝ) := by
    field_simp [hL_ne]
  calc
    (n : ℝ) = 2 * L ^ 2 * ((n : ℝ) / (2 * L ^ 2)) := hcancel.symm
    _ ≤ 2 * L ^ 2 * (m n : ℝ) := hmul
    _ = 2 * (Real.log (n : ℝ)) ^ 2 * (m n : ℝ) := by simp [L]
