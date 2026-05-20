import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteNaturalReducedVertexRatioEventually

open Filter
open scoped Topology

-- [TABLET NODE: NaturalDegreeMassDominatesLogCube]

theorem NaturalDegreeMassDominatesLogCube :
    ∀ A : ℝ, 0 < A →
      ∀ᶠ n : ℕ in Filter.atTop,
        A * (Real.log (n : ℝ)) ^ 3 ≤
          TwoBiteEdgeProbability (1 / 2 : ℝ) n *
            (TwoBiteNaturalReducedVertexCount n : ℝ) := by
-- BODY
  intro A hA
  let m : ℕ → ℕ := fun n => TwoBiteNaturalReducedVertexCount n
  have hm : ∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n := by
    intro n
    rfl
  have hratio := TwoBiteNaturalReducedVertexRatioEventually m hm
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hsmall_real :
      (fun x : ℝ => Real.log x ^ 9) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  have hsmall_nat :
      (fun n : ℕ => Real.log (n : ℝ) ^ 9) =o[atTop]
        (fun n : ℕ => (n : ℝ)) :=
    hsmall_real.comp_tendsto hn_atTop
  have hlog9_eventually :
      ∀ᶠ n : ℕ in atTop,
        16 * A ^ 2 * (Real.log (n : ℝ)) ^ 9 ≤ (n : ℝ) := by
    have hc : 0 < (16 * A ^ 2)⁻¹ := by positivity
    filter_upwards [hsmall_nat.def hc, eventually_ge_atTop (1 : ℕ)]
      with n hbound hn_ge_one
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hlog9_nonneg : 0 ≤ Real.log (n : ℝ) ^ 9 := pow_nonneg hlog_nonneg _
    have hnorm := hbound
    rw [Real.norm_of_nonneg hlog9_nonneg, Real.norm_of_nonneg hn_nonneg] at hnorm
    have hmul := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 16 * A ^ 2)
    have hcancel : 16 * A ^ 2 * ((16 * A ^ 2)⁻¹ * (n : ℝ)) = (n : ℝ) := by
      field_simp [hA.ne']
    calc
      16 * A ^ 2 * (Real.log (n : ℝ)) ^ 9
          ≤ 16 * A ^ 2 * ((16 * A ^ 2)⁻¹ * (n : ℝ)) := by
        simpa [mul_assoc] using hmul
      _ = (n : ℝ) := hcancel
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlog_atTop.eventually_ge_atTop (1 : ℝ), hratio, hlog9_eventually]
    with n hn_ge_one hL_ge_one hratio_n hlog9_n
  let L : ℝ := Real.log (n : ℝ)
  let M : ℝ := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_ge_one)
  have hL_ge_one_local : (1 : ℝ) ≤ L := by simpa [L] using hL_ge_one
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_ge_one_local
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hratio_local : (n : ℝ) ≤ 2 * L ^ 2 * M := by
    simpa [m, M, L] using hratio_n
  have hlog9_local : 16 * A ^ 2 * L ^ 9 ≤ (n : ℝ) := by
    simpa [L] using hlog9_n
  have hp_eq : p = (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) := by
    simp [p, TwoBiteEdgeProbability, L]
  have hsquare_ratio :
      ((n : ℝ)) ^ 2 ≤ (2 * L ^ 2 * M) ^ 2 := by
    exact pow_le_pow_left₀ hn_nonneg hratio_local 2
  have hsquare_ratio' :
      ((n : ℝ)) ^ 2 ≤ 4 * L ^ 4 * M ^ 2 := by
    nlinarith [hsquare_ratio]
  have hchain :
      16 * A ^ 2 * L ^ 9 * (n : ℝ) ≤ 4 * L ^ 4 * M ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlog9_local hn_nonneg
    nlinarith
  have hdiv :
      4 * A ^ 2 * L ^ 6 * (n : ℝ) ≤ L * M ^ 2 := by
    have hL3_pos : 0 < 4 * L ^ 3 := by positivity
    have hdiv := div_le_div_of_nonneg_right hchain hL3_pos.le
    have hleft :
        (16 * A ^ 2 * L ^ 9 * (n : ℝ)) / (4 * L ^ 3) =
          4 * A ^ 2 * L ^ 6 * (n : ℝ) := by
      field_simp [hL_pos.ne']
      ring
    have hright :
        (4 * L ^ 4 * M ^ 2) / (4 * L ^ 3) = L * M ^ 2 := by
      field_simp [hL_pos.ne']
    simpa [hleft, hright] using hdiv
  have hsqrt_sq : Real.sqrt (L / (n : ℝ)) ^ 2 = L / (n : ℝ) := by
    rw [Real.sq_sqrt]
    exact div_nonneg hL_nonneg hn_nonneg
  have hsq_goal :
      (A * L ^ 3) ^ 2 ≤ (((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) * M) ^ 2 := by
    have hhalf_sqrt_sq :
        ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) ^ 2 =
          (1 / 4 : ℝ) * (L / (n : ℝ)) := by
      rw [mul_pow, hsqrt_sq]
      ring
    have hright_sq :
        (((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) * M) ^ 2 =
          ((1 / 4 : ℝ) * (L / (n : ℝ))) * M ^ 2 := by
      rw [mul_pow, hhalf_sqrt_sq]
    rw [hright_sq]
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    field_simp [hn_ne]
    nlinarith
  have hleft_nonneg : 0 ≤ A * L ^ 3 := by positivity
  have hright_nonneg :
      0 ≤ ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) * M := by positivity
  have hmain : A * L ^ 3 ≤ ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) * M := by
    exact (sq_le_sq₀ hleft_nonneg hright_nonneg).mp hsq_goal
  change A * L ^ 3 ≤ p * M
  rw [hp_eq]
  exact hmain
