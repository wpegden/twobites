import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Tablet.NaturalParameterApproximation
import Tablet.ParameterHierarchyBaseDAlgebra
import Tablet.ParameterHierarchyEventualComparisons

-- [TABLET NODE: ParameterHierarchyBaseThreshold]

open Filter
open scoped Topology

theorem ParameterHierarchyBaseThreshold :
    ∀ η : ℝ, 0 < η →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 < n →
        let L := Real.log (n : ℝ)
        let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
        let K := TwoBiteNaturalIndependenceScale (1 + η) n
        let k := (K : ℝ)
        let mReal := (n : ℝ) / L ^ 2
        let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
        let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
        let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
        0 < m ∧
          0 ≤ p ∧
          p ≤ (1 / 2 : ℝ) ∧
          1 ≤ 2 * p * m ∧
          kReal ≤ k ∧
          k < kReal + 1 ∧
          m ≤ mReal ∧
          mReal < m + 1 ∧
          K ≤ n ∧
          k < 2 * kReal ∧
          0 < Real.log L ∧
          2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L := by
-- BODY
  intro η hη
  have hκpos : 0 < 1 + η := by linarith
  have hκ_ge_one : (1 : ℝ) ≤ 1 + η := by linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  have hlog_atTop :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn_atTop
  have hloglog_atTop :
      Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_atTop
  have hprod_atTop :
      Tendsto (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ))
        atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ hn_atTop
    filter_upwards [hlog_atTop.eventually_ge_atTop (1 : ℝ)] with n hlog_ge
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      (n : ℝ) = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_ge hn_nonneg
  have hsqrt_atTop :
      Tendsto
        (fun n : ℕ => Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hprod_atTop
  have hkReal_gt_two_eventually :
      ∀ᶠ n : ℕ in atTop,
        2 < (1 + η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    (hsqrt_atTop.const_mul_atTop hκpos).eventually_gt_atTop (2 : ℝ)
  have hlog_le_half_sqrt_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => Real.sqrt x) := by
      simpa [Real.sqrt_eq_rpow] using
        (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num))
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => Real.sqrt (n : ℝ)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 2),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hsqrt_nonneg] at hbound
    exact hbound
  have hlog_le_cuberoot_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ (1 / 4 : ℝ) * (n : ℝ) ^ ((3 : ℝ)⁻¹) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop]
          (fun x : ℝ => x ^ ((3 : ℝ)⁻¹)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ)⁻¹)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def (by norm_num : (0 : ℝ) < 1 / 4),
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hrpow_nonneg : 0 ≤ (n : ℝ) ^ ((3 : ℝ)⁻¹) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] at hbound
    exact hbound
  let cK : ℝ := 1 / (4 * (1 + η) ^ 2)
  have hcK_pos : 0 < cK := by
    dsimp [cK]
    exact one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hκpos))
  have hlog_le_linear_eventually :
      ∀ᶠ n : ℕ in atTop,
        Real.log (n : ℝ) ≤ cK * (n : ℝ) := by
    have hsmall_real :
        (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) := by
      simpa [Real.rpow_one] using
        (isLittleO_log_rpow_atTop (r := (1 : ℝ)) zero_lt_one)
    have hsmall_nat :
        (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
          (fun n : ℕ => (n : ℝ)) :=
      hsmall_real.comp_tendsto hn_atTop
    filter_upwards [hsmall_nat.def hcK_pos,
      eventually_ge_atTop (1 : ℕ)] with n hbound hn_ge_one
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
      exact Real.log_nonneg hnreal
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hn_nonneg] at hbound
    exact hbound
  have hbase_eventually :
      ∀ᶠ n : ℕ in atTop,
        2 ≤ n ∧
          1 < Real.log (n : ℝ) ∧
          1 ≤ Real.log (Real.log (n : ℝ)) ∧
          2 < (1 + η) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ∧
          Real.log (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) ∧
          Real.log (n : ℝ) ≤ (1 / 4 : ℝ) * (n : ℝ) ^ ((3 : ℝ)⁻¹) ∧
          Real.log (n : ℝ) ≤ cK * (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ),
      hlog_atTop.eventually_gt_atTop (1 : ℝ),
      hloglog_atTop.eventually_ge_atTop (1 : ℝ),
      hkReal_gt_two_eventually,
      hlog_le_half_sqrt_eventually,
      hlog_le_cuberoot_eventually,
      hlog_le_linear_eventually] with n hn_two hL_gt_one hlogL_ge_one
        hkReal_gt_two hL_le_half_sqrt hL_le_cuberoot hL_le_linear
    exact ⟨hn_two, hL_gt_one, hlogL_ge_one, hkReal_gt_two,
      hL_le_half_sqrt, hL_le_cuberoot, hL_le_linear⟩
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp hbase_eventually
  refine ⟨n0, ?_⟩
  intro n hn
  have hbase := hn0 n (le_of_lt hn)
  rcases hbase with
    ⟨hn_two, hL_gt_one, hlogL_ge_one, hkReal_gt_two,
      hL_le_half_sqrt, hL_le_cuberoot, hL_le_linear⟩
  let L := Real.log (n : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  let K := TwoBiteNaturalIndependenceScale (1 + η) n
  let k := (K : ℝ)
  let mReal := (n : ℝ) / L ^ 2
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t1 := Real.sqrt ((n : ℝ) * L) / Real.log L
  have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn_pos : 0 < (n : ℝ) := by
    have hn_one : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hn_two)
    exact lt_trans zero_lt_one hn_one
  have hL_pos : 0 < L := by
    dsimp [L]
    exact lt_trans zero_lt_one hL_gt_one
  have hL_nonneg : 0 ≤ L := hL_pos.le
  have hlogL_pos : 0 < Real.log L := by
    dsimp [L]
    exact lt_of_lt_of_le zero_lt_one hlogL_ge_one
  have hkReal_nonneg : 0 ≤ kReal := by
    dsimp [kReal, L]
    exact mul_nonneg hκpos.le (Real.sqrt_nonneg _)
  have hm_scale_nonneg : 0 ≤ TwoBiteReducedVertexCount n := by
    dsimp [TwoBiteReducedVertexCount, TwoBiteStretch, L]
    exact div_nonneg hn_nonneg (sq_nonneg L)
  have hk_scale_nonneg : 0 ≤ TwoBiteIndependenceScale (1 + η) n := by
    dsimp [TwoBiteIndependenceScale, L]
    exact mul_nonneg hκpos.le (Real.sqrt_nonneg _)
  obtain ⟨hm_le_scale, hscale_lt_m_add, hscale_le_k, hk_lt_scale_add⟩ :=
    NaturalParameterApproximation (1 + η) n hm_scale_nonneg hk_scale_nonneg
  have hm_le_mReal : m ≤ mReal := by
    simpa [m, mReal, TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount,
      TwoBiteStretch, L] using hm_le_scale
  have hmReal_lt_m_add : mReal < m + 1 := by
    simpa [m, mReal, TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount,
      TwoBiteStretch, L] using hscale_lt_m_add
  have hkReal_le_k : kReal ≤ k := by
    simpa [k, K, kReal, TwoBiteNaturalIndependenceScale, TwoBiteIndependenceScale,
      L] using hscale_le_k
  have hk_lt_kReal_add : k < kReal + 1 := by
    simpa [k, K, kReal, TwoBiteNaturalIndependenceScale, TwoBiteIndependenceScale,
      L] using hk_lt_scale_add
  have hLsq_le_quarter_n : L ^ 2 ≤ (1 / 4 : ℝ) * (n : ℝ) := by
    have hright_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (n : ℝ) := by
      positivity
    have hsquare := pow_le_pow_left₀ hL_nonneg
      (by simpa [L] using hL_le_half_sqrt) 2
    have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt hn_nonneg
    nlinarith
  have hmReal_gt_two : 2 < mReal := by
    have hLsq_pos : 0 < L ^ 2 := sq_pos_of_pos hL_pos
    have h2Lsq_lt_n : 2 * L ^ 2 < (n : ℝ) := by
      nlinarith [hLsq_le_quarter_n, hn_pos]
    dsimp [mReal]
    rw [lt_div_iff₀ hLsq_pos]
    simpa [mul_comm] using h2Lsq_lt_n
  have hm_pos : 0 < m := by
    nlinarith [hmReal_gt_two, hmReal_lt_m_add]
  have hLcube_bound : 4 * L ^ 3 ≤ (n : ℝ) := by
    have hcube := pow_le_pow_left₀ hL_nonneg
      (by simpa [L] using hL_le_cuberoot) 3
    have hrpow_cube : ((n : ℝ) ^ ((3 : ℝ)⁻¹)) ^ 3 = (n : ℝ) := by
      simpa using Real.rpow_inv_natCast_pow (x := (n : ℝ)) hn_nonneg
        (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith [hcube, hrpow_cube]
  have hp_mReal_ge_one : 1 ≤ p * mReal := by
    have hdiv_nonneg : 0 ≤ L / (n : ℝ) := div_nonneg hL_nonneg hn_nonneg
    have hprod_nonneg : 0 ≤ p * mReal := by
      dsimp [p, mReal]
      positivity
    have hsquare_eq : (p * mReal) ^ 2 = (n : ℝ) / (4 * L ^ 3) := by
      dsimp [p, mReal]
      rw [mul_pow, mul_pow, Real.sq_sqrt hdiv_nonneg]
      field_simp [hL_pos.ne', hn_pos.ne']
      ring
    rw [← sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) hprod_nonneg]
    rw [hsquare_eq]
    field_simp [hL_pos.ne', hn_pos.ne']
    nlinarith [hLcube_bound, sq_nonneg L]
  have hmReal_half_le_m : mReal / 2 ≤ m := by
    nlinarith [hmReal_gt_two, hmReal_lt_m_add]
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hp_le_half : p ≤ (1 / 2 : ℝ) := by
    have hL_le_n : L ≤ (n : ℝ) := by
      dsimp [L]
      exact Real.log_le_self hn_nonneg
    have hdiv_le_one : L / (n : ℝ) ≤ 1 := by
      rw [div_le_one₀ hn_pos]
      exact hL_le_n
    have hsqrt_le_one : Real.sqrt (L / (n : ℝ)) ≤ 1 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by simpa using hdiv_le_one⟩
    dsimp [p]
    nlinarith
  have htwo_p_nonneg : 0 ≤ 2 * p := by
    exact mul_nonneg (by norm_num) hp_nonneg
  have hp_mReal_le_two_pm : p * mReal ≤ 2 * p * m := by
    have hmul := mul_le_mul_of_nonneg_left hmReal_half_le_m htwo_p_nonneg
    convert hmul using 1
    ring
  have h_one_le_two_pm : 1 ≤ 2 * p * m :=
    le_trans hp_mReal_ge_one hp_mReal_le_two_pm
  have hkReal_add_le_n : kReal + 1 ≤ (n : ℝ) := by
    have hsqrt_le :
        Real.sqrt ((n : ℝ) * L) ≤ (n : ℝ) / (2 * (1 + η)) := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · calc
          (n : ℝ) * L ≤ (n : ℝ) * (cK * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (by simpa [L] using hL_le_linear) hn_nonneg
          _ = ((n : ℝ) / (2 * (1 + η))) ^ 2 := by
            dsimp [cK]
            field_simp [hκpos.ne']
            ring
    have hkReal_le_half : kReal ≤ (n : ℝ) / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsqrt_le hκpos.le
      dsimp [kReal]
      field_simp [hκpos.ne'] at hmul ⊢
      linarith
    have hn_two_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_two
    have hone_le_half_n : (1 : ℝ) ≤ (n : ℝ) / 2 := by linarith
    calc
      kReal + 1 ≤ (n : ℝ) / 2 + (n : ℝ) / 2 :=
        add_le_add hkReal_le_half hone_le_half_n
      _ = (n : ℝ) := by ring
  have hK_le_n : K ≤ n := by
    have hk_lt_n : (K : ℝ) < (n : ℝ) := by
      dsimp [k] at hk_lt_kReal_add
      exact lt_of_lt_of_le hk_lt_kReal_add hkReal_add_le_n
    exact le_of_lt (by exact_mod_cast hk_lt_n)
  have hk_lt_two_kReal : k < 2 * kReal := by
    have hone_lt_kReal : (1 : ℝ) < kReal := lt_trans one_lt_two hkReal_gt_two
    calc
      k < kReal + 1 := hk_lt_kReal_add
      _ < kReal + kReal := by
        simpa [add_comm] using add_lt_add_left hone_lt_kReal kReal
      _ = 2 * kReal := by ring
  have hsqrt_nL_pos : 0 < Real.sqrt ((n : ℝ) * L) := by
    exact Real.sqrt_pos.mpr (mul_pos hn_pos hL_pos)
  have hD : 2 * k / t1 + 1 ≤ 5 * (1 + η) * Real.log L := by
    have hk_expanded :
        k < 2 * ((1 + η) * Real.sqrt ((n : ℝ) * L)) := by
      simpa [kReal] using hk_lt_two_kReal
    dsimp [t1]
    exact ParameterHierarchyBaseDAlgebra (1 + η)
      (Real.sqrt ((n : ℝ) * L)) (Real.log L) k hκ_ge_one
      hsqrt_nL_pos hlogL_pos hlogL_ge_one hk_expanded
  exact ⟨hm_pos, hp_nonneg, hp_le_half, h_one_le_two_pm, hkReal_le_k,
    hk_lt_kReal_add, hm_le_mReal, hmReal_lt_m_add, hK_le_n, hk_lt_two_kReal,
    hlogL_pos, hD⟩
