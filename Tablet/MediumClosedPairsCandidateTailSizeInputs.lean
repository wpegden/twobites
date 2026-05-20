import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic
import Tablet.MediumClosedPairsWitnessSizeCeilPackage
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyBaseThreshold

open Filter
open scoped Topology BigOperators

set_option maxHeartbeats 800000

-- [TABLET NODE: MediumClosedPairsCandidateTailSizeInputs]

theorem MediumClosedPairsCandidateTailSizeInputs
    (ε ε1 ε2 : ℝ) (n0 : ℕ)
    (hparam : ParameterHierarchy ε ε1 ε2 n0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ {m : ℕ},
        let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
        let S : ℕ := Nat.ceil
          (((K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
              TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
        ∀ (i : {I : Finset (Fin n) // I.card = K} ×
              (Fin S → TwoBiteBaseVertex m))
          (π : Fin n ↪ (Fin m × Fin m)),
          let I : Finset (Fin n) := i.1.1
          let coverB : Finset (TwoBiteBaseVertex m) := Finset.univ.image i.2
          let BR : Finset (Fin m) :=
            Finset.univ.filter (fun r : Fin m => Sum.inl r ∈ coverB)
          let BB : Finset (Fin m) :=
            Finset.univ.filter (fun b : Fin m => Sum.inr b ∈ coverB)
          let PR : Finset (Fin m) := I.image (fun v => (π v).1)
          let PB : Finset (Fin m) := I.image (fun v => (π v).2)
          ((BR.card + BB.card : ℝ) ≤
              (3 / 2 : ℝ) * (K : ℝ) *
                Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)) ∧
            PR.card ≤ K ∧ PB.card ≤ K := by
-- BODY
  classical
  rcases hparam with
    ⟨hε2_pos, hε2_lt_ε1, hε1_lt_ε, _hε_lt_one, hε_lt_sixteen,
      _hthree, _hsqrt, _hn0large, _hcomp⟩
  have hε1_pos : 0 < ε1 := lt_trans hε2_pos hε2_lt_ε1
  have hε_pos : 0 < ε := lt_trans hε1_pos hε1_lt_ε
  have hpow_exp_pos : 0 < (1 / 4 : ℝ) - 2 * ε := by
    linarith
  have hn_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop (R := ℝ)
  obtain ⟨Nbase, hbase⟩ := ParameterHierarchyBaseThreshold ε hε_pos
  have hpow_big_eventually :
      ∀ᶠ n : ℕ in atTop,
        (8 : ℝ) ≤ Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 2 * ε) :=
    ((tendsto_rpow_atTop hpow_exp_pos).comp hn_atTop).eventually_ge_atTop (8 : ℝ)
  have hlog_ge_one_eventually :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp hn_atTop).eventually_ge_atTop (1 : ℝ)
  filter_upwards [eventually_gt_atTop Nbase, eventually_ge_atTop (1 : ℕ),
    hpow_big_eventually, hlog_ge_one_eventually] with n hnbase hn_ge_one hpow_big hlog_ge_one
  intro m K S i π I coverB BR BB PR PB
  have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le Nbase) hnbase
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn_ge_one_real : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_one
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog_ge_one
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
    MediumClosedPairsWitnessSizeCeilPackage (n := n) (m := m) (k := K)
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
  let redImage : Finset (TwoBiteBaseVertex m) :=
    BR.image (fun r : Fin m => (Sum.inl r : TwoBiteBaseVertex m))
  let blueImage : Finset (TwoBiteBaseVertex m) :=
    BB.image (fun b : Fin m => (Sum.inr b : TwoBiteBaseVertex m))
  have hred_card : redImage.card = BR.card := by
    dsimp [redImage]
    simpa using
      (Finset.card_image_of_injective BR
        (fun _ _ h => Sum.inl.inj h))
  have hblue_card : blueImage.card = BB.card := by
    dsimp [blueImage]
    simpa using
      (Finset.card_image_of_injective BB
        (fun _ _ h => Sum.inr.inj h))
  have hdisjoint : Disjoint redImage blueImage := by
    rw [Finset.disjoint_left]
    intro x hxred hxblue
    rcases Finset.mem_image.mp hxred with ⟨r, _hr, hrx⟩
    rcases Finset.mem_image.mp hxblue with ⟨b, _hb, hbx⟩
    rw [← hrx] at hbx
    cases hbx
  have hunion_subset : redImage ∪ blueImage ⊆ coverB := by
    intro x hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
      exact (Finset.mem_filter.mp hr).2
    · rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
      exact (Finset.mem_filter.mp hb).2
  have hunion_card :
      (redImage ∪ blueImage).card = BR.card + BB.card := by
    rw [Finset.card_union_of_disjoint hdisjoint, hred_card, hblue_card]
  have hcover_card : coverB.card ≤ S := by
    dsimp [coverB]
    calc
      (Finset.univ.image i.2).card ≤ (Finset.univ : Finset (Fin S)).card :=
        Finset.card_image_le
      _ = S := by simp
  have hcenters_nat : BR.card + BB.card ≤ S := by
    rw [← hunion_card]
    exact le_trans (Finset.card_le_card hunion_subset) hcover_card
  have hcenters_real : ((BR.card + BB.card : ℕ) : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast hcenters_nat
  have hsize :
      ((BR.card + BB.card : ℕ) : ℝ) ≤
        (3 / 2 : ℝ) * (K : ℝ) * rsmall :=
    le_trans hcenters_real hSfinal
  have hPR : PR.card ≤ K := by
    dsimp [PR, I]
    calc
      (i.1.1.image fun v => (π v).1).card ≤ i.1.1.card :=
        Finset.card_image_le
      _ = K := i.1.2
  have hPB : PB.card ≤ K := by
    dsimp [PB, I]
    calc
      (i.1.1.image fun v => (π v).2).card ≤ i.1.1.card :=
        Finset.card_image_le
      _ = K := i.1.2
  exact ⟨by simpa [rsmall] using hsize, hPR, hPB⟩
