import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.TwoBiteConditionalIntersectionBound
import Tablet.OppositeProjectionBlueConditioning
import Tablet.OppositeProjectionBlueExposureTailBound
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.OppositeProjectionIntersectionContainment
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionBlueExposureAveraging
import Tablet.OppositeProjectionPairBadTailFromContainment
import Tablet.OppositeProjectionTailPowerExponentialBound
import Tablet.OppositeProjectionBinomialTailBaseReduction
import Tablet.OppositeProjectionTailBaseEstimate
import Tablet.TwoBiteEventProbabilityUnionBound

-- [TABLET NODE: OppositeProjectionSymmetricBlueBadEventExponentialBound]

theorem OppositeProjectionSymmetricBlueBadEventExponentialBound :
    ∀ m : ℕ → ℕ,
      (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
            (fun ω =>
              let sizeBound : Prop :=
                ∀ x : TwoBiteBaseVertex (m n),
                ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                  2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
              let blueBad : Prop :=
                ∃ b c : Fin (m n), b ≠ c ∧
                (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                      (TwoBiteRedProjection ω)) ∩
                    ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                      (TwoBiteRedProjection ω))).card : ℝ)
                  >
                  (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                    100 * (Real.log (n : ℝ)) ^ 3))
              sizeBound ∧ blueBad) ≤
            (m n : ℝ) ^ 2 * Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
-- BODY
  classical
  intro m hm
  let c : ℝ := 100 * Real.log (50 / Real.exp 1)
  refine ⟨c, ?_, ?_⟩
  · have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp_lt_50 : Real.exp 1 < 50 := by
      linarith [Real.exp_one_lt_three]
    have hratio : 1 < 50 / Real.exp 1 := by
      rw [lt_div_iff₀ hexp_pos]
      simpa using hexp_lt_50
    have hlog : 0 < Real.log (50 / Real.exp 1) := Real.log_pos hratio
    positivity
  · have hReducedRatio :
        ∀ᶠ n : ℕ in Filter.atTop,
          2 ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
      have htend_real :
          Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) Filter.atTop (nhds 0) :=
        Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
      have htend_nat :
          Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (1 * (n : ℝ) + 0))
            Filter.atTop (nhds 0) :=
        htend_real.comp tendsto_natCast_atTop_atTop
      have hsmall :
          ∀ᶠ n : ℕ in Filter.atTop,
            Real.log (n : ℝ) ^ 2 / (n : ℝ) ≤ (1 / 2 : ℝ) := by
        have hnhds : Set.Iic (1 / 2 : ℝ) ∈ nhds (0 : ℝ) := Iic_mem_nhds (by norm_num)
        simpa using (htend_nat hnhds)
      filter_upwards [hsmall, Filter.eventually_ge_atTop (3 : ℕ)] with n hsmall hn3
      have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn3)
      have hlog_pos : 0 < Real.log (n : ℝ) := by
        have hthree : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
        have hone_lt : (1 : ℝ) < (n : ℝ) := by nlinarith
        exact Real.log_pos hone_lt
      have hlog_sq_pos : 0 < Real.log (n : ℝ) ^ 2 := sq_pos_of_pos hlog_pos
      have hlog_sq_le_half_n :
          Real.log (n : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (n : ℝ) := by
        exact (div_le_iff₀ hn_pos).1 hsmall
      rw [le_div_iff₀ hlog_sq_pos]
      nlinarith
    filter_upwards [OppositeProjectionEdgeProbBounds, hReducedRatio, Filter.eventually_ge_atTop (3 : ℕ)]
      with n hp hReducedRatio_n hn3
    let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let pairEvent : Fin (m n) × Fin (m n) → TwoBiteSample n (m n) p → Prop :=
      fun pair ω =>
        let sizeBound : Prop :=
          ∀ x : TwoBiteBaseVertex (m n),
          ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
            2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
        let pairBad : Prop :=
          pair.1 ≠ pair.2 ∧
          (((((TwoBiteLiftedNeighborhood ω (Sum.inr pair.1)).image
                (TwoBiteRedProjection ω)) ∩
              ((TwoBiteLiftedNeighborhood ω (Sum.inr pair.2)).image
                (TwoBiteRedProjection ω))).card : ℝ)
            >
            (((TwoBiteLiftedNeighborhood ω (Sum.inr pair.1) ∩
                TwoBiteLiftedNeighborhood ω (Sum.inr pair.2)).card : ℝ) +
              100 * (Real.log (n : ℝ)) ^ 3))
        sizeBound ∧ pairBad
    have h_event_eq :
        (fun ω : TwoBiteSample n (m n) p =>
          let sizeBound : Prop :=
            ∀ x : TwoBiteBaseVertex (m n),
            ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
              2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
          let blueBad : Prop :=
            ∃ b c : Fin (m n), b ≠ c ∧
            (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                  (TwoBiteRedProjection ω)) ∩
                ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                  (TwoBiteRedProjection ω))).card : ℝ)
              >
              (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                100 * (Real.log (n : ℝ)) ^ 3))
          sizeBound ∧ blueBad) =
          (fun ω => ∃ pair : Fin (m n) × Fin (m n), pairEvent pair ω) := by
      funext ω
      dsimp [pairEvent]
      apply propext
      constructor
      · rintro ⟨hsize, b, d, hbd, hbad⟩
        exact ⟨(b, d), hsize, hbd, hbad⟩
      · rintro ⟨⟨b, d⟩, hsize, hbd, hbad⟩
        exact ⟨hsize, b, d, hbd, hbad⟩
    have hpair :
        ∀ pair : Fin (m n) × Fin (m n),
          TwoBiteEventProbability n (m n) p (pairEvent pair) ≤
            Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
      intro pair
      by_cases hpair_eq : pair.1 = pair.2
      · have hzero : TwoBiteEventProbability n (m n) p (pairEvent pair) = 0 := by
          unfold TwoBiteEventProbability
          simp [pairEvent, hpair_eq]
        rw [hzero]
        exact (Real.exp_pos _).le
      · refine
          OppositeProjectionBlueConditioning n (m n) p (pairEvent pair)
            (Real.exp (-c * (Real.log (n : ℝ)) ^ 3))
            (Real.exp_pos _).le hp.1 hp.2 ?_
        intro G_B ρ
        let U : Finset (Fin n) := Finset.univ.filter (fun v => G_B.Adj pair.1 (ρ v))
        let V : Finset (Fin n) := Finset.univ.filter (fun v => G_B.Adj pair.2 (ρ v))
        let U₀ : Finset (Fin n) := U \ V
        let V₀ : Finset (Fin n) := V \ U
        have hUV : ∀ v : Fin n, v ∈ U₀ → v ∈ V₀ → False := by
          intro v hvU hvV
          simp [U₀, V₀] at hvU hvV
          exact hvU.2 hvV.1
        have hrows : ∀ u : Fin n, u ∈ U₀ → ∀ v : Fin n, v ∈ V₀ → ρ u ≠ ρ v := by
          intro u hu v hv huv
          simp [U₀, V₀, U, V] at hu hv
          exact hv.2 (by simpa [huv] using hu.1)
        have htailReady :
            ∀ η : U₀ → Fin (m n),
              TwoBiteConditionalProbability n (m n) p
                (fun ω => (V₀.filter (fun v =>
                  (ω.2.2 v).1 ∈ (Finset.univ.image η))).card ≥
                  Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3))
                (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
                  (fun (u : U₀) => (ω.2.2 u.1).1) = η)
              ≤
                (Nat.choose V₀.card (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) : ℝ) *
                  (((Finset.univ.image η).card : ℝ) / (m n : ℝ)) ^
                    Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) := by
          intro η
          exact
            OppositeProjectionBlueExposureTailBound n (m n) p U₀ V₀
              (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) G_B ρ η hUV hrows
        have hExposureAverage :
            ∀ B : ℝ, 0 ≤ B →
              (∀ η : U₀ → Fin (m n),
                TwoBiteEventProbability n (m n) p
                    (fun ω => pairEvent pair ω ∧
                      (ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
                        (fun (u : U₀) => (ω.2.2 u.1).1) = η))
                  ≤ B * TwoBiteEventProbability n (m n) p
                    (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
                      (fun (u : U₀) => (ω.2.2 u.1).1) = η)) →
              TwoBiteConditionalProbability n (m n) p (pairEvent pair)
                  (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ) ≤ B := by
          intro B hB hbranch
          exact
            OppositeProjectionBlueExposureAveraging U₀ G_B ρ (pairEvent pair)
              hp.1 hp.2 hB hbranch
        have hTailFromPairBad :
            ∀ η : U₀ → Fin (m n), ∀ ω : TwoBiteSample n (m n) p,
              pairEvent pair ω →
              (ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
                (fun (u : U₀) => (ω.2.2 u.1).1) = η) →
              Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) ≤
                (V₀.filter (fun v =>
                  (ω.2.2 v).1 ∈ (Finset.univ.image η))).card := by
          intro η ω hpairEvent hcell
          have hblue_left :
              TwoBiteLiftedNeighborhood ω (Sum.inr pair.1) = U := by
            ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteBlueGraph, TwoBiteBlueProjection,
              TwoBiteEmbedding, U, hcell.1, congrFun hcell.2.1 v]
          have hblue_right :
              TwoBiteLiftedNeighborhood ω (Sum.inr pair.2) = V := by
            ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteBlueGraph, TwoBiteBlueProjection,
              TwoBiteEmbedding, V, hcell.1, congrFun hcell.2.1 v]
          have hη_agree : ∀ u : U₀, TwoBiteRedProjection ω u.1 = η u := by
            intro u
            simpa [TwoBiteRedProjection] using congrFun hcell.2.2 u
          have hbad_UV :
              (((U.image (TwoBiteRedProjection ω)) ∩
                    (V.image (TwoBiteRedProjection ω))).card : ℝ)
                > (((U ∩ V).card : ℝ) +
                    100 * (Real.log (n : ℝ)) ^ 3) := by
            dsimp [pairEvent] at hpairEvent
            rcases hpairEvent with ⟨_hsize, _hneq, hbad⟩
            simpa [hblue_left, hblue_right] using hbad
          simpa [V₀] using
            (OppositeProjectionPairBadTailFromContainment U V U₀
              (TwoBiteRedProjection ω) η (100 * (Real.log (n : ℝ)) ^ 3)
              rfl hη_agree hbad_UV)
        have hTailPowerExponential :
            ∀ A : ℝ, 0 ≤ A → A ≤ Real.exp 1 / 50 →
              A ^ Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) ≤
                Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
          intro A hA0 hA
          have htceil :
              100 * (Real.log (n : ℝ)) ^ 3 ≤
                (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ) :=
            Nat.le_ceil _
          simpa [c] using
            (OppositeProjectionTailPowerExponentialBound A (Real.log (n : ℝ))
              (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) hA0 hA htceil)
        have hBinomialTailBaseReduction :
            ∀ η : U₀ → Fin (m n), 0 < (m n : ℝ) →
              (Nat.choose V₀.card (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) : ℝ) *
                  (((Finset.univ.image η).card : ℝ) / (m n : ℝ)) ^
                    Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) ≤
                ((Real.exp 1 * (V₀.card : ℝ) *
                    ((Finset.univ.image η).card : ℝ)) /
                  ((Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ) *
                    (m n : ℝ))) ^
                  Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) := by
          intro η hm_pos
          exact
            OppositeProjectionBinomialTailBaseReduction V₀.card (m n)
              (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3))
              ((Finset.univ.image η).card : ℝ) (by positivity) hm_pos
        let B : ℝ := Real.exp (-c * (Real.log (n : ℝ)) ^ 3)
        have hB_nonneg : 0 ≤ B := by
          dsimp [B]
          exact (Real.exp_pos _).le
        have hc_pos_local : 0 < c := by
          dsimp [c]
          have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
          have hexp_lt_50 : Real.exp 1 < 50 := by
            linarith [Real.exp_one_lt_three]
          have hratio : 1 < 50 / Real.exp 1 := by
            rw [lt_div_iff₀ hexp_pos]
            simpa using hexp_lt_50
          have hlog : 0 < Real.log (50 / Real.exp 1) := Real.log_pos hratio
          positivity
        have hn_pos_global : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) hn3)
        have hlog_pos_global : 0 < Real.log (n : ℝ) := by
          have hthree : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
          have hone_lt : (1 : ℝ) < (n : ℝ) := by nlinarith
          exact Real.log_pos hone_lt
        have hB_le_one : B ≤ 1 := by
          dsimp [B]
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by
            have hcube_nonneg : 0 ≤ (Real.log (n : ℝ)) ^ 3 :=
              pow_nonneg hlog_pos_global.le 3
            nlinarith [hc_pos_local, hcube_nonneg])
        have hweight :
            ∀ ω : TwoBiteSample n (m n) p, 0 ≤ TwoBiteSampleWeight ω := by
          intro ω
          exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
        have hprob_nonneg :
            ∀ E : TwoBiteSample n (m n) p → Prop,
              0 ≤ TwoBiteEventProbability n (m n) p E := by
          intro E
          unfold TwoBiteEventProbability
          exact Finset.sum_nonneg (by
            intro ω hω
            exact hweight ω)
        have hprob_mono :
            ∀ {A C : TwoBiteSample n (m n) p → Prop},
              (∀ ω, A ω → C ω) →
              TwoBiteEventProbability n (m n) p A ≤
                TwoBiteEventProbability n (m n) p C := by
          intro A C hAC
          unfold TwoBiteEventProbability
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro ω hω
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
              exact hAC ω hω)
            (by
              intro ω _ _
              exact hweight ω)
        refine hExposureAverage B hB_nonneg ?_
        intro η
        let cell : TwoBiteSample n (m n) p → Prop :=
          fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
            (fun (u : U₀) => (ω.2.2 u.1).1) = η
        let tail : TwoBiteSample n (m n) p → Prop :=
          fun ω => (V₀.filter (fun v =>
            (ω.2.2 v).1 ∈ (Finset.univ.image η))).card ≥
            Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)
        change
          TwoBiteEventProbability n (m n) p
              (fun ω => pairEvent pair ω ∧ cell ω)
            ≤ B * TwoBiteEventProbability n (m n) p cell
        by_cases hex : ∃ ω : TwoBiteSample n (m n) p, pairEvent pair ω ∧ cell ω
        · rcases hex with ⟨ω₀, hω₀_pair, hω₀_cell⟩
          have hsizeω₀ :
              ∀ x : TwoBiteBaseVertex (m n),
                ((TwoBiteLiftedNeighborhood ω₀ x).card : ℝ) ≤
                  2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ) := by
            dsimp [pairEvent] at hω₀_pair
            exact hω₀_pair.1
          have hblue_left₀ :
              TwoBiteLiftedNeighborhood ω₀ (Sum.inr pair.1) = U := by
            ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteBlueGraph, TwoBiteBlueProjection,
              TwoBiteEmbedding, U, hω₀_cell.1, congrFun hω₀_cell.2.1 v]
          have hblue_right₀ :
              TwoBiteLiftedNeighborhood ω₀ (Sum.inr pair.2) = V := by
            ext v
            simp [TwoBiteLiftedNeighborhood, TwoBiteBlueGraph, TwoBiteBlueProjection,
              TwoBiteEmbedding, V, hω₀_cell.1, congrFun hω₀_cell.2.1 v]
          have hU_card_le : (U.card : ℝ) ≤ 2 * p * (n : ℝ) := by
            have hraw := hsizeω₀ (Sum.inr pair.1)
            simpa [hblue_left₀, p] using hraw
          have hV_card_le : (V.card : ℝ) ≤ 2 * p * (n : ℝ) := by
            have hraw := hsizeω₀ (Sum.inr pair.2)
            simpa [hblue_right₀, p] using hraw
          have hU₀_card_le_U : U₀.card ≤ U.card := by
            apply Finset.card_le_card
            intro v hv
            simp [U₀] at hv
            exact hv.1
          have hV₀_card_le_V : V₀.card ≤ V.card := by
            apply Finset.card_le_card
            intro v hv
            simp [V₀] at hv
            exact hv.1
          have hU₀_card_le : (U₀.card : ℝ) ≤ 2 * p * (n : ℝ) := by
            exact le_trans (by exact_mod_cast hU₀_card_le_U) hU_card_le
          have hV₀_card_le : (V₀.card : ℝ) ≤ 2 * p * (n : ℝ) := by
            exact le_trans (by exact_mod_cast hV₀_card_le_V) hV_card_le
          have himage_card_le_U₀ :
              (Finset.univ.image η).card ≤ U₀.card := by
            simpa using
              (Finset.card_image_le (s := (Finset.univ : Finset U₀)) (f := η))
          have himage_card_le : ((Finset.univ.image η).card : ℝ) ≤ 2 * p * (n : ℝ) := by
            exact le_trans (by exact_mod_cast himage_card_le_U₀) hU₀_card_le
          have htwo_pn_nonneg : 0 ≤ 2 * p * (n : ℝ) := by
            have hp_nonneg : 0 ≤ p := by simpa [p] using hp.1
            positivity
          have htwo_pn_sq :
              (2 * p * (n : ℝ)) * (2 * p * (n : ℝ)) =
                Real.log (n : ℝ) * (n : ℝ) := by
            dsimp [p, TwoBiteEdgeProbability]
            ring_nf
            rw [Real.sq_sqrt]
            · field_simp [ne_of_gt hn_pos_global]
            · exact div_nonneg hlog_pos_global.le hn_pos_global.le
          have hVq_le :
              (V₀.card : ℝ) * ((Finset.univ.image η).card : ℝ) ≤
                Real.log (n : ℝ) * (n : ℝ) := by
            calc
              (V₀.card : ℝ) * ((Finset.univ.image η).card : ℝ)
                  ≤ (2 * p * (n : ℝ)) * (2 * p * (n : ℝ)) := by
                    exact mul_le_mul hV₀_card_le himage_card_le (by positivity) htwo_pn_nonneg
              _ = Real.log (n : ℝ) * (n : ℝ) := htwo_pn_sq
          have hmReal_lt_m_add :
              (n : ℝ) / (Real.log (n : ℝ)) ^ 2 < (m n : ℝ) + 1 := by
            simpa [hm n, TwoBiteNaturalReducedVertexCount, TwoBiteReducedVertexCount,
              TwoBiteStretch] using
                (Nat.lt_floor_add_one
                  (a := (n : ℝ) / (Real.log (n : ℝ)) ^ 2))
          have hm_lower :
              (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) ≤ (m n : ℝ) := by
            have hxhalf_le :
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) / 2 ≤
                  (m n : ℝ) := by
              nlinarith [hReducedRatio_n, hmReal_lt_m_add]
            have hrewrite :
                ((n : ℝ) / (Real.log (n : ℝ)) ^ 2) / 2 =
                  (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) := by
              field_simp [ne_of_gt (sq_pos_of_pos hlog_pos_global)]
            simpa [hrewrite] using hxhalf_le
          have hm_pos : 0 < (m n : ℝ) := by
            have hlower_pos :
                0 < (n : ℝ) / (2 * (Real.log (n : ℝ)) ^ 2) := by
              positivity
            exact lt_of_lt_of_le hlower_pos hm_lower
          have ht_lower :
              100 * (Real.log (n : ℝ)) ^ 3 ≤
                (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ) :=
            Nat.le_ceil _
          have ht_pos :
              0 < (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ) := by
            have hraw : 0 < 100 * (Real.log (n : ℝ)) ^ 3 := by
              positivity
            exact lt_of_lt_of_le hraw ht_lower
          let A : ℝ :=
            (Real.exp 1 * (V₀.card : ℝ) *
              ((Finset.univ.image η).card : ℝ)) /
              ((Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ) * (m n : ℝ))
          have hA_nonneg : 0 ≤ A := by
            dsimp [A]
            positivity
          have hA_le : A ≤ Real.exp 1 / 50 := by
            dsimp [A]
            exact
              OppositeProjectionTailBaseEstimate (Real.log (n : ℝ)) (n : ℝ)
                (m n : ℝ)
                (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) : ℝ)
                (V₀.card : ℝ) ((Finset.univ.image η).card : ℝ)
                hlog_pos_global hn_pos_global hm_lower ht_lower hVq_le
          have htail_factor_le_B :
              (Nat.choose V₀.card (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) : ℝ) *
                  (((Finset.univ.image η).card : ℝ) / (m n : ℝ)) ^
                    Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) ≤ B := by
            have hbase := hBinomialTailBaseReduction η hm_pos
            have hpow := hTailPowerExponential A hA_nonneg hA_le
            exact le_trans hbase (by simpa [A, B] using hpow)
          have hcond_tail_B :
              TwoBiteConditionalProbability n (m n) p tail cell ≤ B := by
            exact le_trans (by simpa [tail, cell] using htailReady η) htail_factor_le_B
          have htail_inter_bound :
              TwoBiteEventProbability n (m n) p (fun ω => tail ω ∧ cell ω) ≤
                TwoBiteEventProbability n (m n) p cell * min (1 : ℝ) B := by
            exact
              TwoBiteConditionalIntersectionBound
                (n := n) (m := m n) (p := p)
                (cellBound := TwoBiteEventProbability n (m n) p cell)
                (condBound := B) (event := tail) (condition := cell)
                hweight (hprob_nonneg cell) hB_nonneg le_rfl hcond_tail_B
          have htail_cell_bound :
              TwoBiteEventProbability n (m n) p (fun ω => tail ω ∧ cell ω) ≤
                B * TwoBiteEventProbability n (m n) p cell := by
            have hmin : min (1 : ℝ) B = B := min_eq_right hB_le_one
            simpa [hmin, mul_comm] using htail_inter_bound
          have hpair_tail_subset :
              ∀ ω : TwoBiteSample n (m n) p,
                pairEvent pair ω ∧ cell ω → tail ω ∧ cell ω := by
            intro ω hω
            exact
              ⟨by
                simpa [tail] using hTailFromPairBad η ω hω.1 (by simpa [cell] using hω.2),
                hω.2⟩
          exact le_trans (hprob_mono hpair_tail_subset) htail_cell_bound
        · have hnot :
              ∀ ω : TwoBiteSample n (m n) p, ¬ (pairEvent pair ω ∧ cell ω) := by
            intro ω hω
            exact hex ⟨ω, hω⟩
          have hzero :
              TwoBiteEventProbability n (m n) p
                (fun ω => pairEvent pair ω ∧ cell ω) = 0 := by
            unfold TwoBiteEventProbability
            simp [hnot]
          rw [hzero]
          exact mul_nonneg hB_nonneg (hprob_nonneg cell)
    change
      TwoBiteEventProbability n (m n) p
        (fun ω =>
          let sizeBound : Prop :=
            ∀ x : TwoBiteBaseVertex (m n),
            ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
              2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
          let blueBad : Prop :=
            ∃ b c : Fin (m n), b ≠ c ∧
            (((((TwoBiteLiftedNeighborhood ω (Sum.inr b)).image
                  (TwoBiteRedProjection ω)) ∩
                ((TwoBiteLiftedNeighborhood ω (Sum.inr c)).image
                  (TwoBiteRedProjection ω))).card : ℝ)
              >
              (((TwoBiteLiftedNeighborhood ω (Sum.inr b) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inr c)).card : ℝ) +
                100 * (Real.log (n : ℝ)) ^ 3))
          sizeBound ∧ blueBad) ≤
        (m n : ℝ) ^ 2 * Real.exp (-c * (Real.log (n : ℝ)) ^ 3)
    rw [h_event_eq]
    calc
      TwoBiteEventProbability n (m n) p
          (fun ω => ∃ pair : Fin (m n) × Fin (m n), pairEvent pair ω)
          ≤ ∑ pair : Fin (m n) × Fin (m n),
              TwoBiteEventProbability n (m n) p (pairEvent pair) := by
            exact TwoBiteEventProbabilityUnionBound hp.1 hp.2 pairEvent
      _ ≤ ∑ _pair : Fin (m n) × Fin (m n),
              Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
            apply Finset.sum_le_sum
            intro pair _
            exact hpair pair
      _ = (m n : ℝ) ^ 2 * Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
            simp [Fintype.card_prod, pow_two, mul_assoc]
