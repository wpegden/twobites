import Tablet.NegligibleProbability
import Tablet.WithHighProbability
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.FiberAndDegreeConcentration
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.MediumClosedPairsFailureDeterministicWitness
import Tablet.MediumClosedPairsExponentialEnvelopeNegligible
import Tablet.MediumClosedPairsHierarchyTailInputs
import Tablet.MediumClosedPairsNaturalFixedPairTail
import Tablet.MediumClosedPairsNaturalTailHypotheses
import Tablet.MediumClosedPairsNormalizedCoordinateUnionBridge
import Tablet.MediumClosedPairsEmbeddingCellCoordinateUnionBridge
import Tablet.MediumClosedPairsBadOnRegularExponentialUpperBound
import Tablet.MediumClosedPairsDeterministicWitnessCandidatePackage
import Tablet.MediumClosedPairsWitnessSizeCeilPackage
import Tablet.MediumClosedPairsCandidateCellTail
import Tablet.MediumClosedPairsCandidateCoordinateImplication
import Tablet.MediumClosedPairsCandidateTailSizeInputs
import Tablet.MediumClosedPairsCeilCountExponentEnvelope
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount

set_option maxHeartbeats 2000000

-- [TABLET NODE: MediumClosedPairsBound]

theorem MediumClosedPairsBound :
    ∀ (ε ε1 ε2 β : ℝ) (n0 : ℕ) (m k : ℕ → ℕ),
      ParameterHierarchy ε ε1 ε2 n0 →
      β = (1 / 2 : ℝ) →
      (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
      (∀ n : ℕ, k n = TwoBiteNaturalIndependenceScale (1 + ε) n) →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
            (fun ω => TwoBiteMediumClosedPairsEvent (k := k n) ε ε1 ω)) := by
-- BODY
  classical
  intro ε ε1 ε2 β n0 m k hHierarchy hβ hm hk
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => TwoBiteMediumClosedPairsEvent (k := k n) ε ε1 ω
  let R : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => FiberAndDegreeEvent ω ε2
  have hHierarchyCopy := hHierarchy
  rcases hHierarchyCopy with
    ⟨hε2_pos, _, _, _, _, _, _, _, hEventually⟩
  have hR :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) := by
    simpa [p, R] using FiberAndDegreeConcentration ε2 β hε2_pos hβ m hm
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [Filter.eventually_gt_atTop n0] with n hn
    intro ω
    have hcomp := hEventually n hn
    dsimp only at hcomp
    rcases hcomp with ⟨_, hp_nonneg, hp_le_half, _⟩
    have hp_nonneg' : 0 ≤ TwoBiteEdgeProbability β n := by
      simpa [hβ, TwoBiteEdgeProbability] using hp_nonneg
    have hp_le_one' : TwoBiteEdgeProbability β n ≤ 1 := by
      have hp_le_half' : TwoBiteEdgeProbability β n ≤ (1 / 2 : ℝ) := by
        simpa [hβ, TwoBiteEdgeProbability] using hp_le_half
      exact le_trans hp_le_half' (by norm_num)
    simpa [p] using TwoBiteSampleWeightNonnegative ω hp_nonneg' hp_le_one'
  have hBad :
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => ¬ Good n ω ∧ R n ω)) := by
    classical
    change Filter.Tendsto
      (fun n => TwoBiteEventProbability n (m n) (p n)
        (fun ω => ¬ Good n ω ∧ R n ω)) Filter.atTop (nhds (0 : ℝ))
    have hHierarchyFull := hHierarchy
    rcases hHierarchyFull with
      ⟨hε2_pos_full, hε2_lt_ε1, hε1_lt_ε, hε_lt_one,
        hε_lt_sixteen, _hthree0, _hsqrt0, _hn0large, hcomp⟩
    have hε1_pos : 0 < ε1 := lt_trans hε2_pos_full hε2_lt_ε1
    have hε_pos : 0 < ε := lt_trans hε1_pos hε1_lt_ε
    obtain ⟨Nbase, hbase⟩ := ParameterHierarchyBaseThreshold ε hε_pos
    have hceil_count := MediumClosedPairsCeilCountExponentEnvelope ε ε1 ε2 n0 hHierarchy
    rcases hceil_count with ⟨hcount_eventually, henvelope⟩
    have htail_size_eventually :=
      MediumClosedPairsCandidateTailSizeInputs ε ε1 ε2 n0 hHierarchy
    have hcompressed_eventually :=
      MediumClosedPairsCompressedTailAbsorptions ε hε_pos
    have hn_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop (R := ℝ)
    have hlog_ge_one_eventually :
        ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
      (Real.tendsto_log_atTop.comp hn_atTop).eventually_ge_atTop (1 : ℝ)
    have hnonneg :
        ∀ᶠ n in Filter.atTop,
          0 ≤ TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ R n ω) := by
      filter_upwards [hweight] with n hω_nonneg
      unfold TwoBiteEventProbability
      exact Finset.sum_nonneg (by
        intro ω _hω
        exact hω_nonneg ω)
    have hupper :
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ R n ω)
            ≤
          Real.exp
            ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                Real.log (n : ℝ) +
              3 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
                Real.log (n : ℝ) -
              Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) := by
      filter_upwards [Filter.eventually_gt_atTop n0,
        Filter.eventually_gt_atTop Nbase, Filter.eventually_ge_atTop (2 : ℕ),
        hlog_ge_one_eventually, hcount_eventually, htail_size_eventually,
        hcompressed_eventually] with n hn0 hnbase hn_ge_two hlog_ge_one
        hcount_n htail_size_n hcompressed_n
      let M : ℕ := m n
      let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
      let S : ℕ := Nat.ceil
        (((K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
            TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
      let countExp : ℝ :=
        (K : ℝ) * Real.log (n : ℝ) +
          3 * (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
            Real.log (n : ℝ)
      let tailExp : ℝ := Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)
      let Index :=
        {I : Finset (Fin n) // I.card = K} ×
          (Fin S → TwoBiteBaseVertex M)
      let Candidate : Index → TwoBiteSample n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n) → Prop :=
        fun i ω =>
          let I : Finset (Fin n) := i.1.1
          let coverB : Finset (TwoBiteBaseVertex M) := Finset.univ.image i.2
          ¬ ClosedPairsBound
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ)
              ε1 (K : ℝ) ∧
            ∃ B : Finset (TwoBiteBaseVertex M),
              let A0 := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
              B.Nonempty ∧
              B.card ≤ S ∧
              B ⊆ coverB ∧
              (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
              A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
              (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
                ≤ A0 + TwoBiteLargeCutoff ε n ∧
              (B.card : ℝ) * TwoBiteSmallCutoff ε n
                ≤ A0 + TwoBiteLargeCutoff ε n ∧
              (let redCenters : Finset (Fin M) :=
                  Finset.univ.filter (fun r : Fin M => Sum.inl r ∈ B)
               let blueCenters : Finset (Fin M) :=
                  Finset.univ.filter (fun b : Fin M => Sum.inr b ∈ B)
               let redProjection : Finset (Fin M) := I.image (TwoBiteRedProjection ω)
               let blueProjection : Finset (Fin M) := I.image (TwoBiteBlueProjection ω)
               let normalize : Fin M × Fin M → Fin M × Fin M :=
                  fun e => if e.1.val < e.2.val then e else (e.2, e.1)
               let redOrdered : Finset (Fin M × Fin M) :=
                  @Finset.filter (Fin M × Fin M)
                    (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
                    (Classical.decPred _)
                    (redCenters.product redProjection)
               let blueOrdered : Finset (Fin M × Fin M) :=
                  @Finset.filter (Fin M × Fin M)
                    (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
                    (Classical.decPred _)
                    (blueCenters.product blueProjection)
               let redEdges : Finset (Fin M × Fin M) := redOrdered.image normalize
               let blueEdges : Finset (Fin M × Fin M) := blueOrdered.image normalize
               A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
                ((redEdges.card + blueEdges.card : ℕ) : ℝ))
      have hcover_fun :
          ∀ B : Finset (TwoBiteBaseVertex M),
            B.Nonempty → B.card ≤ S →
              ∃ f : Fin S → TwoBiteBaseVertex M, B ⊆ Finset.univ.image f := by
        intro B hBne hBcard
        obtain ⟨b0, _hb0⟩ := hBne
        have hcard_sub :
            Fintype.card {x // x ∈ B} ≤ Fintype.card (Fin S) := by
          rw [Fintype.card_coe, Fintype.card_fin]
          exact hBcard
        obtain ⟨e : {x // x ∈ B} ↪ Fin S⟩ :=
          Function.Embedding.nonempty_of_card_le hcard_sub
        let f : Fin S → TwoBiteBaseVertex M :=
          fun j =>
            if h : ∃ x : {x // x ∈ B}, e x = j then
              (Classical.choose h).1
            else
              b0
        refine ⟨f, ?_⟩
        intro x hx
        refine Finset.mem_image.mpr ?_
        refine ⟨e ⟨x, hx⟩, Finset.mem_univ _, ?_⟩
        dsimp [f]
        let hw : ∃ y : {x // x ∈ B}, e y = e ⟨x, hx⟩ := ⟨⟨x, hx⟩, rfl⟩
        simp only [dif_pos hw]
        have hchoose : e (Classical.choose hw) = e ⟨x, hx⟩ :=
          Classical.choose_spec hw
        exact congrArg Subtype.val (e.injective hchoose)
      have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le n0) hn0
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hL_pos : 0 < Real.log (n : ℝ) :=
        ParameterHierarchyLogPositivity hcomp hn0
      have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hL_pos
      have hcomp_n := hcomp n hn0
      dsimp only at hcomp_n
      rcases hcomp_n with
        ⟨_hm_pos_comp, hp_nonneg_comp, hp_le_half_comp, _hpm_comp,
          _hk_lower_comp, _hk_succ_comp, _hm_le_comp, _hm_lt_comp,
          _h4eps, _h2klog, _hmedium_terms, _hexp_choose, _hchoose_terms,
          _h4log, _ht1k, _hchoose_t1, _hlin1, _hlin2, _hlin3, _hlin4,
          _hthree_eps, _hε2_nonneg_comp, hε2_le_one_comp, _hpmt1,
          _htouched1, _htouched2, _htouched3, ht2_scale, _hlarge_huge,
          _hhuge_expr, _hlarge_cutoff_lower, _hk_large, _ht3_sq, _hk_tail,
          _hfinalpoly, _henv2, _henv_last⟩
      have hbase_n := hbase n hnbase
      dsimp only at hbase_n
      rcases hbase_n with
        ⟨_hm_pos_base, _hp_base, _hp_le_half_base, _hpm_base, hk_lower_base,
          _hk_succ_base, hm_le_base, _hm_lt_base, _hK_le_n_base, hk_upper_base,
          _hloglog_base, _ht1_base⟩
      have hp0 : 0 ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
        simpa [TwoBiteEdgeProbability] using hp_nonneg_comp
      have hp1 : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ 1 := by
        have hp_half : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := by
          simpa [TwoBiteEdgeProbability] using hp_le_half_comp
        exact le_trans hp_half (by norm_num)
      have hp_pos : 0 < TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
        dsimp [TwoBiteEdgeProbability]
        have hdiv_pos : 0 < Real.log (n : ℝ) / (n : ℝ) :=
          div_pos hL_pos hn_pos
        exact mul_pos (by norm_num) (Real.sqrt_pos.2 hdiv_pos)
      have hp_lt : TwoBiteEdgeProbability (1 / 2 : ℝ) n < 1 :=
        by
          have hp_half : TwoBiteEdgeProbability (1 / 2 : ℝ) n ≤ (1 / 2 : ℝ) := by
            simpa [TwoBiteEdgeProbability] using hp_le_half_comp
          exact lt_of_le_of_lt hp_half (by norm_num)
      have hA_nonneg :
          0 ≤ (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
        exact mul_nonneg (Nat.cast_nonneg K)
          (Real.rpow_pos_of_pos hn_pos _).le
      have hLargeCutoff_pos : 0 < TwoBiteLargeCutoff ε n := by
        dsimp [TwoBiteLargeCutoff]
        exact Real.rpow_pos_of_pos hn_pos _
      have hScale :
          TwoBiteLargeCutoff ε n *
              ((K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε))
            ≤ ε1 * (K : ℝ) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left
          (by simpa [K, TwoBiteLargeCutoff] using ht2_scale)
          (Nat.cast_nonneg K)
        calc
          TwoBiteLargeCutoff ε n *
              ((K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε))
              = (K : ℝ) *
                (TwoBiteLargeCutoff ε n *
                  Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)) := by ring
          _ ≤ (K : ℝ) * (ε1 * (K : ℝ)) := by
                simpa [K, TwoBiteLargeCutoff] using hmul
          _ = ε1 * (K : ℝ) ^ 2 := by ring
      have hChargeFactor :
          (1 + ε2) * (Real.log (n : ℝ)) ^ 2
            ≤ 3 * (Real.log (n : ℝ)) ^ 2 := by
        have hone : (1 + ε2 : ℝ) ≤ 3 := by linarith
        exact mul_le_mul_of_nonneg_right hone (sq_nonneg _)
      have hL3_pos : 0 < 3 * (Real.log (n : ℝ)) ^ 2 := by
        positivity
      have hWitness :
          ∀ ω : TwoBiteSample n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n),
            (¬ TwoBiteMediumClosedPairsEvent (k := K) ε ε1 ω ∧
              FiberAndDegreeEvent ω ε2) →
            ∃ I : Finset (Fin n),
              I.card = K ∧
              ¬ ClosedPairsBound
                ((TwoBiteClosedPairsInClass ω I
                  (TwoBiteMediumClass ω ε I)).card : ℝ)
                ε1 (K : ℝ) ∧
              ∃ B : Finset (TwoBiteBaseVertex M),
                let A0 := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε)
                B.Nonempty ∧
                (∀ x ∈ B, TwoBiteMediumClass ω ε I x) ∧
                A0 < (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ)) ∧
                (∑ x ∈ B, ((TwoBiteX ω I x).card : ℝ))
                  ≤ A0 + TwoBiteLargeCutoff ε n ∧
                (B.card : ℝ) * TwoBiteSmallCutoff ε n
                  ≤ A0 + TwoBiteLargeCutoff ε n ∧
                (let redCenters : Finset (Fin M) :=
                    Finset.univ.filter (fun r : Fin M => Sum.inl r ∈ B)
                 let blueCenters : Finset (Fin M) :=
                    Finset.univ.filter (fun b : Fin M => Sum.inr b ∈ B)
                 let redProjection : Finset (Fin M) := I.image (TwoBiteRedProjection ω)
                 let blueProjection : Finset (Fin M) := I.image (TwoBiteBlueProjection ω)
                 let normalize : Fin M × Fin M → Fin M × Fin M :=
                    fun e => if e.1.val < e.2.val then e else (e.2, e.1)
                 let redOrdered : Finset (Fin M × Fin M) :=
                    @Finset.filter (Fin M × Fin M)
                      (fun e => (TwoBiteRedGraph ω).Adj e.1 e.2)
                      (Classical.decPred _)
                      (redCenters.product redProjection)
                 let blueOrdered : Finset (Fin M × Fin M) :=
                    @Finset.filter (Fin M × Fin M)
                      (fun e => (TwoBiteBlueGraph ω).Adj e.1 e.2)
                      (Classical.decPred _)
                      (blueCenters.product blueProjection)
                 let redEdges : Finset (Fin M × Fin M) := redOrdered.image normalize
                 let blueEdges : Finset (Fin M × Fin M) := blueOrdered.image normalize
                 A0 / (6 * (Real.log (n : ℝ)) ^ 2) <
                  ((redEdges.card + blueEdges.card : ℕ) : ℝ)) := by
        intro ω hbadω
        exact
          MediumClosedPairsFailureDeterministicWitness ε ε1 ε2 ω
            hbadω.2 hbadω.1 hA_nonneg hLargeCutoff_pos hScale
            hChargeFactor hL3_pos
      have hceil_pkg :=
        MediumClosedPairsWitnessSizeCeilPackage (n := n) (m := M) (k := K)
          (ε := ε) hn_pos
      have hSsize :
          ∀ B : Finset (TwoBiteBaseVertex M),
            B.Nonempty →
            (B.card : ℝ) * TwoBiteSmallCutoff ε n
              ≤ (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
                  TwoBiteLargeCutoff ε n →
            B.card ≤ S := by
        simpa [S] using hceil_pkg.1
      have hbase_card :
          (Fintype.card (TwoBiteBaseVertex M) : ℝ) ≤ (n : ℝ) ^ 2 := by
        have hcard_eq :
            (Fintype.card (TwoBiteBaseVertex M) : ℝ) = 2 * (M : ℝ) := by
          have hcard_nat : Fintype.card (TwoBiteBaseVertex M) = 2 * M := by
            simp [TwoBiteBaseVertex, Fintype.card_sum]
            omega
          exact_mod_cast hcard_nat
        have hM_eq :
            (M : ℝ) = (TwoBiteNaturalReducedVertexCount n : ℝ) := by
          simp [M, hm n]
        have hM_le_n : (M : ℝ) ≤ (n : ℝ) := by
          rw [hM_eq]
          have hLsq_pos : 0 < (Real.log (n : ℝ)) ^ 2 := sq_pos_of_pos hL_pos
          have hLsq_ge_one : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
            nlinarith [hlog_ge_one]
          calc
            (TwoBiteNaturalReducedVertexCount n : ℝ)
                ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 2 := by
                  simpa using hm_le_base
            _ ≤ (n : ℝ) := by
                  rw [div_le_iff₀ hLsq_pos]
                  calc
                    (n : ℝ) ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
                      simpa using mul_le_mul_of_nonneg_left hLsq_ge_one hn_nonneg
                    _ = (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := rfl
        have hn_ge_two_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge_two
        have hquad : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
          calc
            2 * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
              exact mul_le_mul_of_nonneg_right hn_ge_two_real hn_nonneg
            _ = (n : ℝ) ^ 2 := by ring
        calc
          (Fintype.card (TwoBiteBaseVertex M) : ℝ) = 2 * (M : ℝ) := hcard_eq
          _ ≤ 2 * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hM_le_n (by norm_num)
          _ ≤ (n : ℝ) ^ 2 := hquad
      have hcountExp :
          (K : ℝ) * Real.log (n : ℝ) + 2 * (S : ℝ) * Real.log (n : ℝ)
            ≤ countExp := by
        exact hcount_n
      obtain ⟨_CandidatePkg, _hcoverPkg, hcard⟩ :=
        MediumClosedPairsDeterministicWitnessCandidatePackage
          (n := n) (m := M) (k := K) (S := S)
          (p := TwoBiteEdgeProbability (1 / 2 : ℝ) n)
          (ε := ε) (ε1 := ε1) (ε2 := ε2) (countExp := countExp)
          hWitness hSsize hn_pos hbase_card hcountExp
      have hcover :
          ∀ ω : TwoBiteSample n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n),
            (¬ TwoBiteMediumClosedPairsEvent (k := K) ε ε1 ω ∧
              FiberAndDegreeEvent ω ε2) →
              ∃ i : Index, Candidate i ω := by
        intro ω hbadω
        have hwitness := hWitness ω hbadω
        rcases hwitness with ⟨I, hIcard, hIbad, B, hB⟩
        dsimp only at hB
        rcases hB with
          ⟨hBne, hBmedium, hsum_gt, hsum_le, hBsmall, hcoord⟩
        have hBcard : B.card ≤ S := hSsize B hBne hBsmall
        obtain ⟨f, hBsubset⟩ := hcover_fun B hBne hBcard
        refine ⟨(⟨I, hIcard⟩, f), ?_⟩
        dsimp [Candidate]
        refine ⟨hIbad, B, ?_⟩
        dsimp
        exact ⟨hBne, hBcard, hBsubset, hBmedium, hsum_gt, hsum_le,
          hBsmall, hcoord⟩
      have hpK :
          TwoBiteEdgeProbability (1 / 2 : ℝ) n * (K : ℝ)
            ≤ (1 + ε) * Real.log (n : ℝ) := by
        let L := Real.log (n : ℝ)
        have hK_upper_le : (K : ℝ) ≤ 2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := by
          exact le_of_lt (by simpa [K, L] using hk_upper_base)
        have hp_formula :
            TwoBiteEdgeProbability (1 / 2 : ℝ) n =
              (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) := by
          dsimp [TwoBiteEdgeProbability, L]
        have hsqrt_product :
            Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) = L := by
          have hdiv_nonneg : 0 ≤ L / (n : ℝ) :=
            div_nonneg (by simpa [L] using hL_nonneg) hn_pos.le
          have harg_eq : (L / (n : ℝ)) * ((n : ℝ) * L) = L ^ 2 := by
            field_simp [ne_of_gt hn_pos]
          calc
            Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) =
                Real.sqrt ((L / (n : ℝ)) * ((n : ℝ) * L)) := by
              rw [Real.sqrt_mul hdiv_nonneg]
            _ = Real.sqrt (L ^ 2) := by rw [harg_eq]
            _ = |L| := Real.sqrt_sq_eq_abs L
            _ = L := abs_of_nonneg (by simpa [L] using hL_nonneg)
        calc
          TwoBiteEdgeProbability (1 / 2 : ℝ) n * (K : ℝ)
              ≤ TwoBiteEdgeProbability (1 / 2 : ℝ) n *
                  (2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L))) := by
                exact mul_le_mul_of_nonneg_left hK_upper_le hp0
          _ = (1 + ε) * L := by
                rw [hp_formula]
                calc
                  (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) *
                      (2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L))) =
                      (1 + ε) *
                        (Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L)) := by
                    ring
                  _ = (1 + ε) * L := by rw [hsqrt_product]
          _ = (1 + ε) * Real.log (n : ℝ) := by rfl
      have hcell_tail :
          ∀ i : Index, ∀ π : Fin n ↪ (Fin M × Fin M),
            TwoBiteEventProbability n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
              (fun ω => TwoBiteEmbedding ω = π ∧ Candidate i ω)
            ≤
              Real.exp (-tailExp) *
                TwoBiteEventProbability n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
                  (fun ω => TwoBiteEmbedding ω = π) := by
        intro i π
        let I : Finset (Fin n) := i.1.1
        let coverB : Finset (TwoBiteBaseVertex M) := Finset.univ.image i.2
        let BR : Finset (Fin M) :=
          Finset.univ.filter (fun r : Fin M => Sum.inl r ∈ coverB)
        let BB : Finset (Fin M) :=
          Finset.univ.filter (fun b : Fin M => Sum.inr b ∈ coverB)
        let PR : Finset (Fin M) := I.image (fun v => (π v).1)
        let PB : Finset (Fin M) := I.image (fun v => (π v).2)
        have hsize_pack := htail_size_n (m := M) i π
        dsimp [K, S, I, coverB, BR, BB, PR, PB] at hsize_pack
        rcases hsize_pack with ⟨hsize, hPR, hPB⟩
        have htail_inputs :=
          MediumClosedPairsNaturalTailHypotheses
            (α := Fin M) ε n BR BB hn_pos hL_pos hε_pos hε_lt_one
            hsize (by simpa [K] using hk_lower_base) hpK
            (by simpa using hcompressed_n.1)
            (by simpa using hcompressed_n.2)
        rcases htail_inputs with ⟨hApos, _hp0_tail, hmean, htail⟩
        have himp :
            ∀ ω : TwoBiteSample n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n),
              TwoBiteEmbedding ω = π →
              Candidate i ω →
              let K : ℕ := TwoBiteNaturalIndependenceScale (1 + ε) n
              let A : ℝ := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
                (6 * (Real.log (n : ℝ)) ^ 2)
              let t : ℕ := Nat.ceil A
              let normalize : Fin M × Fin M → Fin M × Fin M :=
                fun e => if e.1.val < e.2.val then e else (e.2, e.1)
              let redRaw : Finset (Fin M × Fin M) :=
                (BR.product PR).filter (fun e => e.1 ≠ e.2)
              let blueRaw : Finset (Fin M × Fin M) :=
                (BB.product PB).filter (fun e => e.1 ≠ e.2)
              let C : Finset (Sum (Fin M × Fin M) (Fin M × Fin M)) :=
                redRaw.image
                    (fun e => (Sum.inl (normalize e) :
                      Sum (Fin M × Fin M) (Fin M × Fin M))) ∪
                  blueRaw.image
                    (fun e => (Sum.inr (normalize e) :
                      Sum (Fin M × Fin M) (Fin M × Fin M)))
              t ≤
                (@Finset.filter (Sum (Fin M × Fin M) (Fin M × Fin M))
                  (fun e => TwoBiteEdgeCoordinateValue ω e)
                  (Classical.decPred _) C).card := by
          intro ω hcell hcand
          have h :=
            MediumClosedPairsCandidateCoordinateImplication
              (n := n) (m := M) (S := S) (ε := ε) (ε1 := ε1) i π ω
          simpa [K, S, I, coverB, BR, BB, PR, PB, Candidate] using
            h hcell hcand
        have htail_bound :=
          MediumClosedPairsCandidateCellTail
            (n := n) (m := M) (ε := ε) π BR BB PR PB
            (Candidate i) hp_pos hp_lt
        simpa [K, tailExp] using
          htail_bound hApos hPR hPB hmean htail himp
      have hbad_bound :
          TwoBiteEventProbability n M (TwoBiteEdgeProbability (1 / 2 : ℝ) n)
            (fun ω =>
              ¬ TwoBiteMediumClosedPairsEvent (k := K) ε ε1 ω ∧
                FiberAndDegreeEvent ω ε2)
          ≤ Real.exp (countExp - tailExp) :=
        MediumClosedPairsBadOnRegularExponentialUpperBound
          (n := n) (m := M) (k := K)
          (p := TwoBiteEdgeProbability (1 / 2 : ℝ) n)
          (ε := ε) (ε1 := ε1) (ε2 := ε2)
          (countExp := countExp) (tailExp := tailExp)
          (ι := Index) Candidate hp0 hp1 hcover hcell_tail hcard
      have htarget :
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ R n ω)
          ≤ Real.exp
            ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                Real.log (n : ℝ) +
              3 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
                Real.log (n : ℝ) -
                      Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) := by
                change
                  TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
                    (fun ω =>
                      ¬ TwoBiteMediumClosedPairsEvent (k := k n) ε ε1 ω ∧
                        FiberAndDegreeEvent ω ε2)
                  ≤ Real.exp
                    ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                        Real.log (n : ℝ) +
                      3 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) *
                        Real.log (n : ℝ) -
                      Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))
                rw [hβ]
                simpa [hk n, M, K, countExp, tailExp] using hbad_bound
      exact htarget
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds henvelope hnonneg hupper
  have hGood :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    WithHighProbabilityOfNegligibleBadOnRegular m p Good R hR hBad hweight
  simpa [p, Good] using hGood
