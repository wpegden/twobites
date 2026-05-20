import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteSample
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeight
import Tablet.WithHighProbability
import Tablet.FixedSetHistoryCellBranchAveraging
import Tablet.TwoBiteConditionalIntersectionBound
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.OppositeProjectionConditioning
import Tablet.OppositeProjectionRowInjectionLaw
import Tablet.OppositeProjectionWTailBound
import Tablet.OppositeProjectionExposureTailBound
import Tablet.OppositeProjectionAsymptoticBound
import Tablet.OppositeProjectionIntersectionContainment
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.OppositeProjectionPairBadTailFromContainment
import Tablet.OppositeProjectionTailPowerExponentialBound
import Tablet.OppositeProjectionBinomialTailBaseReduction
import Tablet.OppositeProjectionTailBaseEstimate

-- [TABLET NODE: OppositeProjectionRedFailureBound]

set_option maxHeartbeats 2000000 in
theorem OppositeProjectionRedFailureBound :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability β n * (n : ℝ)
                let redBound : Prop :=
                  ∀ r s : Fin (m n), r ≠ s →
                  ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                        (TwoBiteBlueProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                        (TwoBiteBlueProjection ω))).card : ℝ)
                    ≤
                    (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3)
                sizeBound → redBound)) := by
-- BODY
  classical
  intro β hβ m hm
  subst β
  let c : ℝ := 100 * Real.log (50 / Real.exp 1)
  have hc_pos : 0 < c := by
    have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    have hexp_lt_50 : Real.exp 1 < 50 := by
      linarith [Real.exp_one_lt_three]
    have hratio : 1 < 50 / Real.exp 1 := by
      rw [lt_div_iff₀ hexp_pos]
      simpa using hexp_lt_50
    have hlog : 0 < Real.log (50 / Real.exp 1) := Real.log_pos hratio
    positivity
  have hBad_tendsto :
      Filter.Tendsto
        (fun n =>
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
            (fun ω =>
              let sizeBound : Prop :=
                ∀ x : TwoBiteBaseVertex (m n),
                ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                  2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
              let redBad : Prop :=
                ∃ r s : Fin (m n), r ≠ s ∧
                (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                      (TwoBiteBlueProjection ω)) ∩
                    ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                      (TwoBiteBlueProjection ω))).card : ℝ)
                  >
                  (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                    100 * (Real.log (n : ℝ)) ^ 3))
              sizeBound ∧ redBad))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hReducedRatio :
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
    have hExp :
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
            (fun ω =>
              let sizeBound : Prop :=
                ∀ x : TwoBiteBaseVertex (m n),
                ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                  2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
              let redBad : Prop :=
                ∃ r s : Fin (m n), r ≠ s ∧
                (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                      (TwoBiteBlueProjection ω)) ∩
                    ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                      (TwoBiteBlueProjection ω))).card : ℝ)
                  >
                  (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                      TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                    100 * (Real.log (n : ℝ)) ^ 3))
              sizeBound ∧ redBad) ≤
            (m n : ℝ) ^ 2 * Real.exp (-c * (Real.log (n : ℝ)) ^ 3) := by
      filter_upwards [OppositeProjectionEdgeProbBounds, hReducedRatio,
        Filter.eventually_ge_atTop (3 : ℕ)] with n hp hReducedRatio_n hn3
      let p : ℝ := TwoBiteEdgeProbability (1 / 2 : ℝ) n
      let pairEvent : Fin (m n) × Fin (m n) → TwoBiteSample n (m n) p → Prop :=
        fun pair ω =>
          let sizeBound : Prop :=
            ∀ x : TwoBiteBaseVertex (m n),
            ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
              2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
          let pairBad : Prop :=
            pair.1 ≠ pair.2 ∧
            (((((TwoBiteLiftedNeighborhood ω (Sum.inl pair.1)).image
                  (TwoBiteBlueProjection ω)) ∩
                ((TwoBiteLiftedNeighborhood ω (Sum.inl pair.2)).image
                  (TwoBiteBlueProjection ω))).card : ℝ)
              >
              (((TwoBiteLiftedNeighborhood ω (Sum.inl pair.1) ∩
                  TwoBiteLiftedNeighborhood ω (Sum.inl pair.2)).card : ℝ) +
                100 * (Real.log (n : ℝ)) ^ 3))
          sizeBound ∧ pairBad
      have h_event_eq :
          (fun ω : TwoBiteSample n (m n) p =>
            let sizeBound : Prop :=
              ∀ x : TwoBiteBaseVertex (m n),
              ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
            let redBad : Prop :=
              ∃ r s : Fin (m n), r ≠ s ∧
              (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                    (TwoBiteBlueProjection ω)) ∩
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                    (TwoBiteBlueProjection ω))).card : ℝ)
                >
                (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                    TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                  100 * (Real.log (n : ℝ)) ^ 3))
            sizeBound ∧ redBad) =
            (fun ω => ∃ pair : Fin (m n) × Fin (m n), pairEvent pair ω) := by
        funext ω
        dsimp [pairEvent]
        apply propext
        constructor
        · rintro ⟨hsize, r, s, hrs, hbad⟩
          exact ⟨(r, s), hsize, hrs, hbad⟩
        · rintro ⟨⟨r, s⟩, hsize, hrs, hbad⟩
          exact ⟨hsize, r, s, hrs, hbad⟩
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
            OppositeProjectionConditioning n (m n) p (pairEvent pair)
              (Real.exp (-c * (Real.log (n : ℝ)) ^ 3))
              (Real.exp_pos _).le
              (fun ω => TwoBiteSampleWeightNonnegative ω hp.1 hp.2) ?_
          intro G_R ρ
          let U : Finset (Fin n) := Finset.univ.filter (fun v => G_R.Adj pair.1 (ρ v))
          let V : Finset (Fin n) := Finset.univ.filter (fun v => G_R.Adj pair.2 (ρ v))
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
                    (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥
                    Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3))
                  (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
                    (fun (u : U₀) => (ω.2.2 u.1).2) = η)
                ≤
                  (Nat.choose V₀.card (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) : ℝ) *
                    (((Finset.univ.image η).card : ℝ) / (m n : ℝ)) ^
                      Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) := by
            intro η
            exact
              OppositeProjectionExposureTailBound n (m n) p U₀ V₀
                (Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3)) G_R ρ η hUV hrows
          have hExposureAverage :
              ∀ B : ℝ, 0 ≤ B →
                (∀ η : U₀ → Fin (m n),
                  TwoBiteEventProbability n (m n) p
                      (fun ω => pairEvent pair ω ∧
                        (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
                          (fun (u : U₀) => (ω.2.2 u.1).2) = η))
                    ≤ B * TwoBiteEventProbability n (m n) p
                      (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
                        (fun (u : U₀) => (ω.2.2 u.1).2) = η)) →
                TwoBiteConditionalProbability n (m n) p (pairEvent pair)
                    (fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ) ≤ B := by
            intro B hB hbranch
            let hist : TwoBiteSample n (m n) p → Prop :=
              fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ
            let firstBranch : (U₀ → Fin (m n)) → TwoBiteSample n (m n) p → Prop :=
              fun η ω => hist ω ∧ (fun (u : U₀) => (ω.2.2 u.1).2) = η
            have hbranch' :
                ∀ η : U₀ → Fin (m n),
                  TwoBiteEventProbability n (m n) p
                      (fun ω => pairEvent pair ω ∧ hist ω ∧ firstBranch η ω)
                    ≤ B * TwoBiteEventProbability n (m n) p (firstBranch η) := by
              intro η
              simpa [hist, firstBranch, and_assoc, and_left_comm, and_comm] using hbranch η
            have havg :
                TwoBiteConditionalProbability n (m n) p
                    (fun ω => pairEvent pair ω ∧ hist ω) hist ≤ B := by
              refine
                @FixedSetHistoryCellBranchAveraging n (m n) p B hist hist
                  (pairEvent pair) (U₀ → Fin (m n)) _ firstBranch hp.1 hp.2 hB ?_ ?_ ?_ ?_
                  hbranch'
              · intro ω h
                exact h
              · intro η ω hη
                exact hη.1
              · intro ω hhist _hfixed
                refine ⟨fun u : U₀ => (ω.2.2 u.1).2, ?_⟩
                exact ⟨hhist, rfl⟩
              · intro η ζ hne ω hboth
                rcases hboth with ⟨hη, hζ⟩
                exact hne (hη.2.symm.trans hζ.2)
            simpa [TwoBiteConditionalProbability, hist, and_assoc, and_left_comm, and_comm] using havg
          have hTailFromPairBad :
              ∀ η : U₀ → Fin (m n), ∀ ω : TwoBiteSample n (m n) p,
                pairEvent pair ω →
                (ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
                  (fun (u : U₀) => (ω.2.2 u.1).2) = η) →
                Nat.ceil (100 * (Real.log (n : ℝ)) ^ 3) ≤
                  (V₀.filter (fun v =>
                    (ω.2.2 v).2 ∈ (Finset.univ.image η))).card := by
            intro η ω hpairEvent hcell
            have hred_left :
                TwoBiteLiftedNeighborhood ω (Sum.inl pair.1) = U := by
              ext v
              simp [TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteRedProjection,
                TwoBiteEmbedding, U, hcell.1, congrFun hcell.2.1 v]
            have hred_right :
                TwoBiteLiftedNeighborhood ω (Sum.inl pair.2) = V := by
              ext v
              simp [TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteRedProjection,
                TwoBiteEmbedding, V, hcell.1, congrFun hcell.2.1 v]
            have hη_agree : ∀ u : U₀, TwoBiteBlueProjection ω u.1 = η u := by
              intro u
              simpa [TwoBiteBlueProjection] using congrFun hcell.2.2 u
            have hbad_UV :
                (((U.image (TwoBiteBlueProjection ω)) ∩
                      (V.image (TwoBiteBlueProjection ω))).card : ℝ)
                  > (((U ∩ V).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3) := by
              dsimp [pairEvent] at hpairEvent
              rcases hpairEvent with ⟨_hsize, _hneq, hbad⟩
              simpa [hred_left, hred_right] using hbad
            simpa [V₀] using
              (OppositeProjectionPairBadTailFromContainment U V U₀
                (TwoBiteBlueProjection ω) η (100 * (Real.log (n : ℝ)) ^ 3)
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
          have hc_pos_local : 0 < c := hc_pos
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
            fun ω => ω.1 = G_R ∧ (fun v => (ω.2.2 v).1) = ρ ∧
              (fun (u : U₀) => (ω.2.2 u.1).2) = η
          let tail : TwoBiteSample n (m n) p → Prop :=
            fun ω => (V₀.filter (fun v =>
              (ω.2.2 v).2 ∈ (Finset.univ.image η))).card ≥
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
            have hred_left₀ :
                TwoBiteLiftedNeighborhood ω₀ (Sum.inl pair.1) = U := by
              ext v
              simp [TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteRedProjection,
                TwoBiteEmbedding, U, hω₀_cell.1, congrFun hω₀_cell.2.1 v]
            have hred_right₀ :
                TwoBiteLiftedNeighborhood ω₀ (Sum.inl pair.2) = V := by
              ext v
              simp [TwoBiteLiftedNeighborhood, TwoBiteRedGraph, TwoBiteRedProjection,
                TwoBiteEmbedding, V, hω₀_cell.1, congrFun hω₀_cell.2.1 v]
            have hU_card_le : (U.card : ℝ) ≤ 2 * p * (n : ℝ) := by
              have hraw := hsizeω₀ (Sum.inl pair.1)
              simpa [hred_left₀, p] using hraw
            have hV_card_le : (V.card : ℝ) ≤ 2 * p * (n : ℝ) := by
              have hraw := hsizeω₀ (Sum.inl pair.2)
              simpa [hred_right₀, p] using hraw
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
            let redBad : Prop :=
              ∃ r s : Fin (m n), r ≠ s ∧
              (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                    (TwoBiteBlueProjection ω)) ∩
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                    (TwoBiteBlueProjection ω))).card : ℝ)
                >
                (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                    TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                  100 * (Real.log (n : ℝ)) ^ 3))
            sizeBound ∧ redBad) ≤
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
    have hnonneg :
        ∀ᶠ n in Filter.atTop,
          (0 : ℝ) ≤
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
              (fun ω =>
                let sizeBound : Prop :=
                  ∀ x : TwoBiteBaseVertex (m n),
                  ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                    2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
                let redBad : Prop :=
                  ∃ r s : Fin (m n), r ≠ s ∧
                  (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                        (TwoBiteBlueProjection ω)) ∩
                      ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                        (TwoBiteBlueProjection ω))).card : ℝ)
                    >
                    (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                        TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                      100 * (Real.log (n : ℝ)) ^ 3))
                sizeBound ∧ redBad) := by
      filter_upwards [OppositeProjectionEdgeProbBounds] with n hp
      exact TwoBiteEventProbabilityNonnegative hp.1 hp.2 _
    exact
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (OppositeProjectionAsymptoticBound c hc_pos m hm) hnonneg hExp
  unfold WithHighProbability
  let pfun : ℕ → ℝ := fun n => TwoBiteEdgeProbability (1 / 2 : ℝ) n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (pfun n) → Prop :=
    fun n ω =>
      let sizeBound : Prop :=
        ∀ x : TwoBiteBaseVertex (m n),
        ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
          2 * pfun n * (n : ℝ)
      let redBound : Prop :=
        ∀ r s : Fin (m n), r ≠ s →
        ((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
              (TwoBiteBlueProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
              (TwoBiteBlueProjection ω))).card : ℝ)
          ≤
          (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3)
      sizeBound → redBound
  let Bad : ∀ n : ℕ, TwoBiteSample n (m n) (pfun n) → Prop :=
    fun n ω =>
      let sizeBound : Prop :=
        ∀ x : TwoBiteBaseVertex (m n),
        ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
          2 * pfun n * (n : ℝ)
      let redBad : Prop :=
        ∃ r s : Fin (m n), r ≠ s ∧
        (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
              (TwoBiteBlueProjection ω)) ∩
            ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
              (TwoBiteBlueProjection ω))).card : ℝ)
          >
          (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
              TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
            100 * (Real.log (n : ℝ)) ^ 3))
      sizeBound ∧ redBad
  have hBad' :
      Filter.Tendsto
        (fun n =>
          TwoBiteEventProbability n (m n) (pfun n) (Bad n))
        Filter.atTop (nhds (0 : ℝ)) := by
    simpa [pfun, Bad] using hBad_tendsto
  have htotal := TwoBiteNaturalTotalMassOneEventually (1 / 2 : ℝ) rfl m hm
  have hprob_eq :
      ∀ᶠ n in Filter.atTop,
        TwoBiteEventProbability n (m n) (pfun n) (Good n) =
          1 - TwoBiteEventProbability n (m n) (pfun n) (Bad n) := by
    filter_upwards [htotal] with n htot
    have hcompl : ∀ ω : TwoBiteSample n (m n) (pfun n), Bad n ω ↔ ¬ Good n ω := by
      intro ω
      dsimp [Bad, Good, pfun]
      constructor
      · rintro ⟨hsize, hbad⟩ hgood
        rcases hbad with ⟨r, s, hne, hgt⟩
        have hle := hgood hsize r s hne
        linarith
      · intro hnot
        by_cases hsize :
            ∀ x : TwoBiteBaseVertex (m n),
              ((TwoBiteLiftedNeighborhood ω x).card : ℝ) ≤
                2 * TwoBiteEdgeProbability (1 / 2 : ℝ) n * (n : ℝ)
        · refine ⟨hsize, ?_⟩
          by_contra hnoBad
          apply hnot
          intro _hsize r s hne
          by_contra hnotle
          have hgt :
              (((((TwoBiteLiftedNeighborhood ω (Sum.inl r)).image
                    (TwoBiteBlueProjection ω)) ∩
                  ((TwoBiteLiftedNeighborhood ω (Sum.inl s)).image
                    (TwoBiteBlueProjection ω))).card : ℝ)
                >
                (((TwoBiteLiftedNeighborhood ω (Sum.inl r) ∩
                    TwoBiteLiftedNeighborhood ω (Sum.inl s)).card : ℝ) +
                  100 * (Real.log (n : ℝ)) ^ 3)) :=
            lt_of_not_ge hnotle
          exact hnoBad ⟨r, s, hne, hgt⟩
        · exfalso
          apply hnot
          intro hsize'
          exact False.elim (hsize hsize')
    have hsum :
        TwoBiteEventProbability n (m n) (pfun n) (Good n) +
          TwoBiteEventProbability n (m n) (pfun n) (Bad n) =
            TwoBiteEventProbability n (m n) (pfun n) (fun _ => True) := by
      unfold TwoBiteEventProbability
      rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hgood : Good n ω
      · have hnotbad : ¬ Bad n ω := by
          intro hbadω
          exact (hcompl ω).1 hbadω hgood
        simp [hgood, hnotbad]
      · have hbadω : Bad n ω := (hcompl ω).2 hgood
        simp [hgood, hbadω]
    have htotal_one :
        TwoBiteEventProbability n (m n) (pfun n) (fun _ => True) = 1 := by
      simpa [pfun] using htot.2
    linarith
  have htend :
      Filter.Tendsto
        (fun n => 1 - TwoBiteEventProbability n (m n) (pfun n) (Bad n))
        Filter.atTop (nhds (1 : ℝ)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have hsub := hconst.sub hBad'
    simpa using hsub
  have hprob_eq_symm :
      (fun n => 1 - TwoBiteEventProbability n (m n) (pfun n) (Bad n))
        =ᶠ[Filter.atTop]
      (fun n => TwoBiteEventProbability n (m n) (pfun n) (Good n)) :=
    hprob_eq.mono (fun n hn => hn.symm)
  have hfinal :
      Filter.Tendsto
        (fun n => TwoBiteEventProbability n (m n) (pfun n) (Good n))
        Filter.atTop (nhds (1 : ℝ)) :=
    Filter.Tendsto.congr' hprob_eq_symm htend
  simpa [pfun, Good] using hfinal
