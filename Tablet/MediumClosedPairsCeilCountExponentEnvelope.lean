import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.MediumClosedPairsWitnessSizeCeilPackage
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyBaseThreshold
import Tablet.ParameterHierarchyT28Threshold
import Tablet.ParameterHierarchyLogPositivity

open Filter
open scoped Topology

set_option maxHeartbeats 1000000

-- [TABLET NODE: MediumClosedPairsCeilCountExponentEnvelope]

theorem MediumClosedPairsCeilCountExponentEnvelope
    (ε ε1 ε2 : ℝ) (n0 : ℕ)
    (hparam : ParameterHierarchy ε ε1 ε2 n0) :
    (∀ᶠ n : ℕ in atTop,
      let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
      let S : ℕ := Nat.ceil
        (((K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
            TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
      (K : ℝ) * Real.log (n : ℝ) + 2 * (S : ℝ) * Real.log (n : ℝ) ≤
        (K : ℝ) * Real.log (n : ℝ) +
          3 * (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
            Real.log (n : ℝ)) ∧
    Tendsto
      (fun n : ℕ =>
        Real.exp
          ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) * Real.log (n : ℝ) +
            3 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * Real.log (n : ℝ) -
            Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)))
      atTop (nhds (0 : ℝ)) := by
-- BODY
  rcases hparam with
    ⟨hε2_pos, hε2_lt_ε1, hε1_lt_ε, _hε_lt_one, hε_lt_sixteen,
      _hthree, _hsqrt, _hn0large, hcomp⟩
  have hε1_pos : 0 < ε1 := lt_trans hε2_pos hε2_lt_ε1
  have hε_pos : 0 < ε := lt_trans hε1_pos hε1_lt_ε
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  obtain ⟨Nbase, hbase⟩ := ParameterHierarchyBaseThreshold ε hε_pos
  constructor
  · have hpow_exp_pos : 0 < (1 / 4 : ℝ) - 2 * ε := by
      linarith
    have hpow_big_eventually :
        ∀ᶠ n : ℕ in atTop,
          (8 : ℝ) ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) :=
      ((tendsto_rpow_atTop hpow_exp_pos).comp hn_atTop).eventually_ge_atTop (8 : ℝ)
    have hlog_ge_one_eventually :
        ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp hn_atTop).eventually_ge_atTop (1 : ℝ)
    filter_upwards [eventually_gt_atTop Nbase, eventually_ge_atTop (1 : ℕ),
      hpow_big_eventually, hlog_ge_one_eventually] with n hnbase hn_ge_one
        hpow_big hlog_ge_one
    intro K S
    have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le Nbase) hnbase
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
    have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog_ge_one
    have hbase_n := hbase n hnbase
    dsimp only at hbase_n
    rcases hbase_n with
      ⟨_hm_pos, _hp_base, _hp_le_half, _hpm, hk_lower, _hk_succ, _hm_le,
        _hm_lt, _hK_le_n, _hk_upper, _hloglog, _ht1⟩
    let rsmall : ℝ := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)
    let rmain : ℝ := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
    have hrsmall_pos : 0 < rsmall := by
      dsimp [rsmall]
      exact Real.rpow_pos_of_pos hn_pos _
    have hsqrt_mul :
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) =
          Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    have hk_lower' :
        (1 + ε) * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) ≤
          (K : ℝ) := by
      simpa [K, hsqrt_mul, mul_assoc] using hk_lower
    have hquarter_le_sqrt :
        Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le hn_ge_one_real (by norm_num)
        _ = Real.sqrt (n : ℝ) := by
          exact (Real.sqrt_eq_rpow (n : ℝ)).symm
    have hsqrt_le_sqrtlog :
        Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
      have hsqrtlog_ge_one : (1 : ℝ) ≤ Real.sqrt (Real.log (n : ℝ)) := by
        have h := Real.sqrt_le_sqrt hlog_ge_one
        simpa using h
      have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      calc
        Real.sqrt (n : ℝ) = Real.sqrt (n : ℝ) * 1 := by ring
        _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrtlog_ge_one hsqrtn_nonneg
    have hsqrtlog_le_kreal :
        Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) ≤
          (1 + ε) * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
      have hone_le : (1 : ℝ) ≤ 1 + ε := by linarith
      have hnonneg :
          0 ≤ Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by positivity
      calc
        Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))
            = 1 * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
        _ ≤ (1 + ε) * (Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hone_le hnonneg
    have hquarter_le_k :
        Real.rpow (n : ℝ) (1 / 4 : ℝ) ≤ (K : ℝ) :=
      le_trans hquarter_le_sqrt (le_trans hsqrt_le_sqrtlog
        (le_trans hsqrtlog_le_kreal hk_lower'))
    have hpowsum_eq :
        Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 2 * ε) + 2 * ε) =
          Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
      congr 1
      ring
    have hpow_mul :
        (8 : ℝ) * Real.rpow (n : ℝ) (2 * ε) ≤
          Real.rpow (n : ℝ) (1 / 4 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hpow_big
        (Real.rpow_pos_of_pos hn_pos (2 * ε)).le
      calc
        (8 : ℝ) * Real.rpow (n : ℝ) (2 * ε)
            ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) *
                Real.rpow (n : ℝ) (2 * ε) := hmul
        _ = Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 2 * ε) + 2 * ε) := by
          exact (Real.rpow_add hn_pos ((1 / 4 : ℝ) - 2 * ε) (2 * ε)).symm
        _ = Real.rpow (n : ℝ) (1 / 4 : ℝ) := hpowsum_eq
    have hn2e_le_eighth_k :
        Real.rpow (n : ℝ) (2 * ε) ≤ (1 / 8 : ℝ) * (K : ℝ) := by
      nlinarith [le_trans hpow_mul hquarter_le_k]
    have hε_le_half : ε ≤ (1 / 2 : ℝ) := by
      linarith
    have hnε_le_sqrt :
        Real.rpow (n : ℝ) ε ≤ Real.sqrt (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) ε ≤ Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
          exact Real.rpow_le_rpow_of_exponent_le hn_ge_one_real hε_le_half
        _ = Real.sqrt (n : ℝ) := by
          exact (Real.sqrt_eq_rpow (n : ℝ)).symm
    have hnε_le_K :
        Real.rpow (n : ℝ) ε ≤ (K : ℝ) :=
      le_trans hnε_le_sqrt (le_trans hsqrt_le_sqrtlog
        (le_trans hsqrtlog_le_kreal hk_lower'))
    have hpow_eps_mul_r :
        Real.rpow (n : ℝ) ε * rsmall =
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) := by
      dsimp [rsmall]
      calc
        Real.rpow (n : ℝ) ε *
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)
            = Real.rpow (n : ℝ) (ε + ((1 / 4 : ℝ) - 3 * ε)) := by
              exact (Real.rpow_add hn_pos ε ((1 / 4 : ℝ) - 3 * ε)).symm
        _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) := by
              congr 1
              ring
    have hpow_le_kr :
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) ≤ (K : ℝ) * rsmall := by
      have hmul := mul_le_mul_of_nonneg_right hnε_le_K hrsmall_pos.le
      calc
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) =
            Real.rpow (n : ℝ) ε * rsmall := hpow_eps_mul_r.symm
        _ ≤ (K : ℝ) * rsmall := hmul
    have hkr_ge_eight : (8 : ℝ) ≤ (K : ℝ) * rsmall :=
      le_trans hpow_big hpow_le_kr
    have hone_le_eighth_kr : (1 : ℝ) ≤ (1 / 8 : ℝ) * ((K : ℝ) * rsmall) := by
      nlinarith
    have hrmain_eq :
        rmain = rsmall * Real.rpow (n : ℝ) (2 * ε) := by
      dsimp [rmain, rsmall]
      calc
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
            = Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 3 * ε) + 2 * ε) := by
              congr 1
              ring
        _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
              Real.rpow (n : ℝ) (2 * ε) := by
              exact Real.rpow_add hn_pos ((1 / 4 : ℝ) - 3 * ε) (2 * ε)
    have hrmain_le_eighth_kr :
        rmain ≤ (1 / 8 : ℝ) * ((K : ℝ) * rsmall) := by
      rw [hrmain_eq]
      have hmul := mul_le_mul_of_nonneg_left hn2e_le_eighth_k hrsmall_pos.le
      nlinarith [hmul]
    have hextra_absorb :
        rmain + 1 ≤ (1 / 2 : ℝ) * ((K : ℝ) * rsmall) := by
      nlinarith [hrmain_le_eighth_kr, hone_le_eighth_kr]
    have hceil_pkg :=
      MediumClosedPairsWitnessSizeCeilPackage (n := n) (m := 0) (k := K)
        (ε := ε) hn_pos
    have hSbound :
        (S : ℝ) ≤ (K : ℝ) * rsmall + rmain + 1 := by
      simpa only [S, rsmall, rmain] using hceil_pkg.2
    have hSfinal :
        (S : ℝ) ≤ (3 / 2 : ℝ) * (K : ℝ) * rsmall := by
      calc
        (S : ℝ) ≤ (K : ℝ) * rsmall + rmain + 1 := hSbound
        _ ≤ (K : ℝ) * rsmall + (1 / 2 : ℝ) * ((K : ℝ) * rsmall) := by
          nlinarith [hextra_absorb]
        _ = (3 / 2 : ℝ) * (K : ℝ) * rsmall := by ring
    have htwiceS :
        2 * (S : ℝ) * Real.log (n : ℝ) ≤
          3 * (K : ℝ) * rsmall * Real.log (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hSfinal hL_nonneg
      nlinarith [hmul]
    nlinarith
  · rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards with n
      have hexp_pos :
          0 <
            Real.exp
              ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) * Real.log (n : ℝ) +
                3 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                  Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * Real.log (n : ℝ) -
                Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) :=
        Real.exp_pos _
      linarith
    · intro b hb
      let δ : ℝ := b / 2
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        linarith
      have hδ_lt_b : δ < b := by
        dsimp [δ]
        linarith
      obtain ⟨N28, h28⟩ :=
        ParameterHierarchyT28Threshold ε 1 hε_pos (by norm_num) hε_lt_sixteen
      have hAexp_pos : 0 < (3 / 4 : ℝ) - 2 * ε := by
        linarith
      have hA_atTop :
          Tendsto
            (fun n : ℕ => Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))
            atTop atTop :=
        (tendsto_rpow_atTop hAexp_pos).comp hn_atTop
      have hdecay_eventually :
          ∀ᶠ n : ℕ in atTop,
            Real.exp
              (-(3 / 8 : ℝ) *
                Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) ≤ δ := by
        filter_upwards [hA_atTop.eventually_ge_atTop
          (max (0 : ℝ) (-(8 / 3 : ℝ) * Real.log δ))] with n hpow_ge
        let A : ℝ := Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)
        have hlog_floor : -(8 / 3 : ℝ) * Real.log δ ≤ A := by
          exact le_trans (le_max_right (0 : ℝ) (-(8 / 3 : ℝ) * Real.log δ))
            (by simpa [A] using hpow_ge)
        have harg_le_log : -(3 / 8 : ℝ) * A ≤ Real.log δ := by
          nlinarith
        exact (Real.le_log_iff_exp_le hδ_pos).1 harg_le_log
      let N : ℕ := max n0 (max Nbase N28)
      filter_upwards [eventually_gt_atTop N, hdecay_eventually] with n hn hdecay
      have hn0 : n0 < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
      have hnbase : Nbase < n := by
        exact lt_of_le_of_lt
          (le_trans (Nat.le_max_left Nbase N28) (Nat.le_max_right n0 (max Nbase N28))) hn
      have hn28 : N28 < n := by
        exact lt_of_le_of_lt
          (le_trans (Nat.le_max_right Nbase N28) (Nat.le_max_right n0 (max Nbase N28))) hn
      have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le n0) hn0
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      have hL_pos : 0 < Real.log (n : ℝ) :=
        ParameterHierarchyLogPositivity hcomp hn0
      have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hL_pos
      have hbase_n := hbase n hnbase
      dsimp at hbase_n
      rcases hbase_n with
        ⟨_hm_pos, _hp_base, _hp_le_half, _hpm, _hk_lower, _hk_succ, _hm_le,
          _hm_lt, _hK_le_n, hk_upper, _hloglog, _ht1⟩
      have h28_n := h28 n hn28
      dsimp at h28_n
      rcases h28_n with ⟨hfirst, hsecond, _htail⟩
      let K := TwoBiteNaturalIndependenceScale (1 + ε) n
      let L := Real.log (n : ℝ)
      let A := Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)
      let e₁ := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε)
      let e₂ := Real.rpow (n : ℝ) ε
      let r := Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)
      have hA_pos : 0 < A := by
        dsimp [A]
        exact Real.rpow_pos_of_pos hn_pos _
      have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
      have he₁_pos : 0 < e₁ := by
        dsimp [e₁]
        exact Real.rpow_pos_of_pos hn_pos _
      have he₂_pos : 0 < e₂ := by
        dsimp [e₂]
        exact Real.rpow_pos_of_pos hn_pos _
      have hr_pos : 0 < r := by
        dsimp [r]
        exact Real.rpow_pos_of_pos hn_pos _
      have hK_upper_alg :
          (K : ℝ) < 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L := by
        have hsqrt_mul :
            Real.sqrt ((n : ℝ) * L) = Real.sqrt (n : ℝ) * Real.sqrt L := by
          exact Real.sqrt_mul (Nat.cast_nonneg n) L
        calc
          (K : ℝ) < 2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := by
            simpa [K, L] using hk_upper
          _ = 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L := by
            rw [hsqrt_mul]
            ring
      have hA_eq_sqrt_e₁ :
          A = Real.sqrt (n : ℝ) * e₁ := by
        dsimp [A, e₁]
        calc
          Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) =
              Real.rpow (n : ℝ) ((1 / 2 : ℝ) + ((1 / 4 : ℝ) - 2 * ε)) := by
            congr 1
            ring
          _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) := by
            exact Real.rpow_add hn_pos (1 / 2 : ℝ) ((1 / 4 : ℝ) - 2 * ε)
          _ = Real.sqrt (n : ℝ) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) :=
            congrArg (fun x : ℝ => x * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε))
              (Real.sqrt_eq_rpow (n : ℝ)).symm
      have hsqrt_mul_e₁ :
          Real.sqrt (n : ℝ) * e₁ = A := hA_eq_sqrt_e₁.symm
      have hr_mul_e₂ :
          r * e₂ = e₁ := by
        dsimp [r, e₂, e₁]
        calc
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * Real.rpow (n : ℝ) ε =
              Real.rpow (n : ℝ) (((1 / 4 : ℝ) - 3 * ε) + ε) := by
            exact (Real.rpow_add hn_pos ((1 / 4 : ℝ) - 3 * ε) ε).symm
          _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) := by
            congr 1
            ring
      have hsqrt_mul_r_e₂ :
          Real.sqrt (n : ℝ) * r * e₂ = A := by
        calc
          Real.sqrt (n : ℝ) * r * e₂ =
              Real.sqrt (n : ℝ) * (r * e₂) := by ring
          _ = Real.sqrt (n : ℝ) * e₁ := by rw [hr_mul_e₂]
          _ = A := hsqrt_mul_e₁
      have hterm₁_upper :
          (K : ℝ) * L ≤ 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by
        have hmul :=
          mul_le_mul_of_nonneg_right (le_of_lt hK_upper_alg) (by simpa [L] using hL_nonneg)
        calc
          (K : ℝ) * L ≤ (2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L) * L := hmul
          _ = 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * L := by ring
      have hterm₁_quarter :
          (K : ℝ) * L ≤ (1 / 4 : ℝ) * A := by
        have hscale :=
          mul_le_mul_of_nonneg_right hfirst hA_nonneg
        have hupper_quarter :
            2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * L ≤
              (1 / 4 : ℝ) * A := by
          calc
            2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * L =
                (2 * (1 + ε) * Real.sqrt L * L / e₁) * A := by
              rw [← hsqrt_mul_e₁]
              field_simp [ne_of_gt he₁_pos]
            _ ≤ (1 / 4 : ℝ) * A := by
              simpa [e₁] using hscale
        exact le_trans hterm₁_upper hupper_quarter
      have hsecond_factor_nonneg :
          0 ≤ 3 * r * L := by
        positivity
      have hterm₂_upper :
          3 * (K : ℝ) * r * L ≤
            6 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L := by
        have hmul :=
          mul_le_mul_of_nonneg_right (le_of_lt hK_upper_alg) hsecond_factor_nonneg
        calc
          3 * (K : ℝ) * r * L = (K : ℝ) * (3 * r * L) := by ring
          _ ≤ (2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L) *
              (3 * r * L) := hmul
          _ = 6 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L := by ring
      have hterm₂_three_eighth :
          3 * (K : ℝ) * r * L ≤ (3 / 8 : ℝ) * A := by
        have hscale :=
          mul_le_mul_of_nonneg_right hsecond hA_nonneg
        have hupper_quarter :
            4 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L ≤
              (1 / 4 : ℝ) * A := by
          calc
            4 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L =
                (4 * (1 + ε) * Real.sqrt L * L / e₂) * A := by
              rw [← hsqrt_mul_r_e₂]
              field_simp [ne_of_gt he₂_pos]
            _ ≤ (1 / 4 : ℝ) * A := by
              simpa [e₂] using hscale
        calc
          3 * (K : ℝ) * r * L
              ≤ 6 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L := hterm₂_upper
          _ = (3 / 2 : ℝ) *
              (4 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L * r * L) := by ring
          _ ≤ (3 / 2 : ℝ) * ((1 / 4 : ℝ) * A) := by
            exact mul_le_mul_of_nonneg_left hupper_quarter (by norm_num)
          _ = (3 / 8 : ℝ) * A := by ring
      have hexponent_le :
          (K : ℝ) * L + 3 * (K : ℝ) * r * L - A ≤
            -(3 / 8 : ℝ) * A := by
        calc
          (K : ℝ) * L + 3 * (K : ℝ) * r * L - A ≤
              (1 / 4 : ℝ) * A + (3 / 8 : ℝ) * A - A :=
            sub_le_sub_right (add_le_add hterm₁_quarter hterm₂_three_eighth) A
          _ = -(3 / 8 : ℝ) * A := by ring
      have hle_delta :
          Real.exp ((K : ℝ) * L + 3 * (K : ℝ) * r * L - A) ≤ δ :=
        le_trans (Real.exp_le_exp.2 hexponent_le) (by simpa [A] using hdecay)
      exact lt_of_le_of_lt (by simpa [K, L, A, r] using hle_delta) hδ_lt_b
