import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalReducedVertexRatioEventually
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.WithinRelativeError

open Filter
open scoped Topology

-- [TABLET NODE: FiberAndDegreeNaturalMeanWithinRelativeError]

theorem FiberAndDegreeNaturalMeanWithinRelativeError :
    ∀ ε : ℝ, 0 < ε →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        ∀ᶠ n : ℕ in Filter.atTop,
          WithinRelativeError ε ((Real.log (n : ℝ)) ^ 2)
            ((n : ℝ) / (m n : ℝ)) := by
-- BODY
  intro ε hε m hm
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hratio := TwoBiteNaturalReducedVertexRatioEventually m hm
  have hsmall_real :
      (fun x : ℝ => Real.log x ^ 2) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  have hsmall_nat :
      (fun n : ℕ => Real.log (n : ℝ) ^ 2) =o[atTop]
        (fun n : ℕ => (n : ℝ)) :=
    hsmall_real.comp_tendsto hn_atTop
  have hlog_sq_small :
      ∀ᶠ n : ℕ in atTop,
        (2 / ε) * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hc : 0 < ε / 2 := by positivity
    filter_upwards [hsmall_nat.def hc, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hlog_sq_nonneg : 0 ≤ Real.log (n : ℝ) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg hlog_sq_nonneg,
      Real.norm_of_nonneg hn_nonneg] at hbound
    calc
      (2 / ε) * (Real.log (n : ℝ)) ^ 2
          ≤ (2 / ε) * ((ε / 2) * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (n : ℝ) := by
        field_simp [hε.ne']
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      hlog_atTop.eventually_ge_atTop (1 : ℝ), hratio, hlog_sq_small]
    with n hn_ge_one hL_ge_one hratio_n hlog_sq_bound
  let L : ℝ := Real.log (n : ℝ)
  let M : ℝ := (m n : ℝ)
  let x : ℝ := (n : ℝ) / L ^ 2
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL_ge_one_local : (1 : ℝ) ≤ L := by simpa [L] using hL_ge_one
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one_local
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hL_sq_pos : 0 < L ^ 2 := sq_pos_of_ne_zero hL_ne
  have hL_sq_nonneg : 0 ≤ L ^ 2 := hL_sq_pos.le
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg hn_nonneg hL_sq_nonneg
  have hM_le_x : M ≤ x := by
    dsimp [M, x]
    rw [hm n, TwoBiteNaturalReducedVertexCount,
      TwoBiteReducedVertexCount, TwoBiteStretch]
    exact Nat.floor_le hx_nonneg
  have hx_lt_M_add_one : x < M + 1 := by
    dsimp [M, x]
    rw [hm n, TwoBiteNaturalReducedVertexCount,
      TwoBiteReducedVertexCount, TwoBiteStretch]
    exact Nat.lt_floor_add_one _
  have hM_large : 1 / ε ≤ M := by
    have hchain : (2 / ε) * L ^ 2 ≤ 2 * L ^ 2 * M := by
      calc
        (2 / ε) * L ^ 2 ≤ (n : ℝ) := by
          simpa [L] using hlog_sq_bound
        _ ≤ 2 * L ^ 2 * M := by
          simpa [L, M] using hratio_n
    have hden_pos : 0 < 2 * L ^ 2 := by positivity
    calc
      1 / ε = ((2 / ε) * L ^ 2) / (2 * L ^ 2) := by
        field_simp [hε.ne', hL_ne]
      _ ≤ (2 * L ^ 2 * M) / (2 * L ^ 2) := by
        exact div_le_div_of_nonneg_right hchain hden_pos.le
      _ = M := by
        field_simp [hL_ne]
  have hM_pos : 0 < M := lt_of_lt_of_le (by positivity : 0 < 1 / ε) hM_large
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have hM_inv_le_eps : 1 / M ≤ ε := by
    rw [div_le_iff₀ hM_pos]
    have hmul := mul_le_mul_of_nonneg_left hM_large hε.le
    have hcancel : ε * (1 / ε) = 1 := by field_simp [hε.ne']
    nlinarith
  have hx_sub_nonneg : 0 ≤ x - M := sub_nonneg.mpr hM_le_x
  have hx_sub_le_one : x - M ≤ 1 := by linarith [hx_lt_M_add_one]
  have hactual_eq :
      (n : ℝ) / M - L ^ 2 = L ^ 2 * ((x - M) / M) := by
    dsimp [x]
    field_simp [hL_ne, hM_ne]
  have hdiff_nonneg : 0 ≤ (n : ℝ) / M - L ^ 2 := by
    rw [hactual_eq]
    exact mul_nonneg hL_sq_nonneg (div_nonneg hx_sub_nonneg hM_pos.le)
  unfold WithinRelativeError
  rw [abs_of_nonneg (by simpa [L, M] using hdiff_nonneg)]
  simpa [L, M] using calc
    (n : ℝ) / M - L ^ 2 = L ^ 2 * ((x - M) / M) := hactual_eq
    _ ≤ L ^ 2 * (1 / M) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hx_sub_le_one hM_pos.le) hL_sq_nonneg
    _ ≤ L ^ 2 * ε := by
      exact mul_le_mul_of_nonneg_left hM_inv_le_eps hL_sq_nonneg
    _ = ε * L ^ 2 := by ring
