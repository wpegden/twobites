import Tablet.ClosedPairsBound
import Tablet.FixedSetExceptionalWitnessClassification
import Tablet.FixedSetOppositeColorTerminalCoverage
import Tablet.LargeClosedPairsBound
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteBlueProjection
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteLargeClass
import Tablet.TwoBiteMediumClass
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.TwoBiteX

-- [TABLET NODE: FixedSetAdaptiveExceptionalCandidates]

theorem FixedSetAdaptiveExceptionalCandidates :
    ∀ {n m k : ℕ} {p ε ε1 ε2 : ℝ} {n0 : ℕ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ωFirst : TwoBiteSample n m p),
      0 ≤ ε1 →
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      m = TwoBiteNaturalReducedVertexCount n →
      p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
      I.card = k →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      hist ωFirst →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
              e ∈ recorded) →
      (∀ e,
        e ∈ terminal ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        (∀ e, e ∈ ER ↔
          e ∈ terminal ∧
            match e with
            | Sum.inl q =>
                ∃ b : Fin m,
                  (TwoBiteLargeClass ωFirst ε I (Sum.inr b) ∨
                    TwoBiteMediumClass ωFirst ε I (Sum.inr b) ∨
                      TwoBiteSmallClass ωFirst ε I (Sum.inr b)) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ωFirst I (Sum.inr b)).image
                        (TwoBiteRedProjection ωFirst))
            | Sum.inr _ => False) ∧
        (∀ e, e ∈ EB ↔
          e ∈ terminal ∧
            match e with
            | Sum.inl _ => False
            | Sum.inr q =>
                ∃ r : Fin m,
                  (TwoBiteLargeClass ωFirst ε I (Sum.inl r) ∨
                    TwoBiteMediumClass ωFirst ε I (Sum.inl r) ∨
                      TwoBiteSmallClass ωFirst ε I (Sum.inl r)) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ωFirst I (Sum.inl r)).image
                        (TwoBiteBlueProjection ωFirst))) ∧
        (∀ ω : TwoBiteSample n m p,
          hist ω →
          (∀ x : Fin n, ω.2.2 x = ωFirst.2.2 x) →
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue ωFirst e)) →
          (∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ωFirst e)) →
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
            ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
            (∀ e,
              e ∈ TwoBiteStagedOpenPairs ω ε I →
              TwoBiteEdgeCoordinateValue ω e →
              (match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) →
              (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) →
                e ∈ ER)) ∧
        (∀ ω : TwoBiteSample n m p,
          hist ω →
          (∀ x : Fin n, ω.2.2 x = ωFirst.2.2 x) →
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue ωFirst e)) →
          (∀ e,
            e ∈ terminal →
              match e with
              | Sum.inl _ =>
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ωFirst e)
              | Sum.inr _ => True) →
          TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
            ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
            (∀ e,
              e ∈ TwoBiteStagedOpenPairs ω ε I →
              TwoBiteEdgeCoordinateValue ω e →
              (match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
              (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) →
                e ∈ EB)) := by
-- BODY
  classical
  intro n m k p ε ε1 ε2 n0 I hist recorded terminal ωFirst
    hε1_nonneg hComparisons hn hm hp hIcard hk hHistFirst hRecorded
    hTerminal hStagedTerminal
  let redExceptional :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl q =>
          ∃ b : Fin m,
            (TwoBiteLargeClass ωFirst ε I (Sum.inr b) ∨
              TwoBiteMediumClass ωFirst ε I (Sum.inr b) ∨
                TwoBiteSmallClass ωFirst ε I (Sum.inr b)) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ωFirst I (Sum.inr b)).image
                  (TwoBiteRedProjection ωFirst))
      | Sum.inr _ => False
  let blueExceptional :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl _ => False
      | Sum.inr q =>
          ∃ r : Fin m,
            (TwoBiteLargeClass ωFirst ε I (Sum.inl r) ∨
              TwoBiteMediumClass ωFirst ε I (Sum.inl r) ∨
                TwoBiteSmallClass ωFirst ε I (Sum.inl r)) ∧
            q ∈
              TwoBiteBasePairs
                ((TwoBiteX ωFirst I (Sum.inl r)).image
                  (TwoBiteBlueProjection ωFirst))
  let ER : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    terminal.filter redExceptional
  let EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    terminal.filter blueExceptional
  have hpClass :
      p = (1 / 2 : ℝ) * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) := by
    simpa [TwoBiteEdgeProbability] using hp
  have hProjectedPair_has_final_pair :
      ∀ (proj : Fin n → Fin m) (X : Finset (Fin n)) (q : Fin m × Fin m),
        q ∈ TwoBiteBasePairs (X.image proj) →
          ∃ a : Fin n × Fin n,
            a ∈ TwoBiteFinalPairs X ∧
              ((proj a.1 = q.1 ∧ proj a.2 = q.2) ∨
                (proj a.1 = q.2 ∧ proj a.2 = q.1)) := by
    intro proj X q hq
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq
    rcases hq with ⟨⟨hq1, hq2⟩, hqrank⟩
    rcases hq1 with ⟨u, huX, huproj⟩
    rcases hq2 with ⟨v, hvX, hvproj⟩
    have huv_ne : u ≠ v := by
      intro huv
      have hqeq : q.1 = q.2 := by
        calc
          q.1 = proj u := huproj.symm
          _ = proj v := by rw [huv]
          _ = q.2 := hvproj
      rw [hqeq] at hqrank
      exact (lt_irrefl q.2) hqrank
    by_cases huv_rank : u.val < v.val
    · refine ⟨(u, v), ?_, Or.inl ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, huX, hvX] using huv_rank
      · exact ⟨huproj, hvproj⟩
    · have hval_ne : u.val ≠ v.val := by
        intro hval
        exact huv_ne (Fin.ext hval)
      have hvu_rank : v.val < u.val := by
        have hle : v.val ≤ u.val := Nat.le_of_not_gt huv_rank
        exact lt_of_le_of_ne hle (Ne.symm hval_ne)
      refine ⟨(v, u), ?_, Or.inr ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, hvX, huX] using hvu_rank
      · exact ⟨hvproj, huproj⟩
  refine ⟨ER, EB, ?_, ?_, ?_, ?_⟩
  · intro e
    simp [ER, redExceptional]
  · intro e
    simp [EB, blueExceptional]
  · intro ω hω hEmb hRecordedAgree hBlueTerminal hRegularity
    constructor
    · have hCoverage :=
        FixedSetOppositeColorTerminalCoverage (I := I)
          (recorded := recorded) (terminal := terminal)
          (ω := ω) (ωFirst := ωFirst)
          hEmb hRecordedAgree (hRecorded ω hω)
          (hRecorded ωFirst hHistFirst) hTerminal
      have hBlueCoverage := hCoverage.1 hBlueTerminal
      have hFiber : FiberAndDegreeEvent ω ε2 := by
        simpa [TwoBiteRegularityEvent] using hRegularity.1
      have hMediumEvent :
          TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω := by
        simpa [TwoBiteRegularityEvent] using hRegularity.2.1
      have hSmallEvent :
          TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω := by
        simpa [TwoBiteRegularityEvent] using hRegularity.2.2
      have hI_scale :
          I.card = TwoBiteNaturalIndependenceScale (1 + ε) n := by
        rw [hIcard, hk]
      have hLargeClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) := by
        have h := LargeClosedPairsBound ω I hComparisons hn hI_scale hFiber
        simpa [hIcard] using h
      have hMediumClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteMediumClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) :=
        hMediumEvent I hIcard
      have hSmallClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteSmallClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) :=
        hSmallEvent I hIcard
      have hTripleClosedBound :
          ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ) +
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) +
                ((TwoBiteClosedPairsInClass ω I
                  (TwoBiteSmallClass ω ε I)).card : ℝ)
            ≤ (3 * ε1) * (k : ℝ) ^ 2 := by
        dsimp [ClosedPairsBound] at hLargeClosed hMediumClosed hSmallClosed
        nlinarith
      let redFirstClassExceptional (cls : TwoBiteBaseVertex m → Prop) :
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
        fun e =>
          match e with
          | Sum.inl q =>
              ∃ b : Fin m,
                cls (Sum.inr b) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ωFirst I (Sum.inr b)).image
                        (TwoBiteRedProjection ωFirst))
          | Sum.inr _ => False
      let ERLarge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (redFirstClassExceptional (TwoBiteLargeClass ωFirst ε I))
      let ERMedium : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (redFirstClassExceptional (TwoBiteMediumClass ωFirst ε I))
      let ERSmall : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (redFirstClassExceptional (TwoBiteSmallClass ωFirst ε I))
      have hRedExceptional_cases :
          ∀ e, redExceptional e →
            redFirstClassExceptional (TwoBiteLargeClass ωFirst ε I) e ∨
              redFirstClassExceptional (TwoBiteMediumClass ωFirst ε I) e ∨
                redFirstClassExceptional (TwoBiteSmallClass ωFirst ε I) e := by
        intro e he
        cases e with
        | inl q =>
            dsimp [redExceptional, redFirstClassExceptional] at he ⊢
            rcases he with ⟨b, hbClass, hq⟩
            rcases hbClass with hbLarge | hbRest
            · exact Or.inl ⟨b, hbLarge, hq⟩
            · rcases hbRest with hbMedium | hbSmall
              · exact Or.inr (Or.inl ⟨b, hbMedium, hq⟩)
              · exact Or.inr (Or.inr ⟨b, hbSmall, hq⟩)
        | inr q =>
            dsimp [redExceptional] at he
      have hER_subset_class_union :
          ER ⊆ ERLarge ∪ ERMedium ∪ ERSmall := by
        intro e he
        have hpack : e ∈ terminal ∧ redExceptional e := by
          simpa [ER] using (Finset.mem_filter.mp he)
        have hterm : e ∈ terminal := hpack.1
        have hred : redExceptional e := hpack.2
        rcases hRedExceptional_cases e hred with hlarge | hrest
        · simp [ERLarge, hterm, hlarge]
        · rcases hrest with hmedium | hsmall
          · simp [ERMedium, hterm, hmedium]
          · simp [ERSmall, hterm, hsmall]
      have hER_card_le_class_union :
          ER.card ≤ ERLarge.card + ERMedium.card + ERSmall.card := by
        have hsub :
            ER.card ≤ (ERLarge ∪ ERMedium ∪ ERSmall).card :=
          Finset.card_le_card hER_subset_class_union
        have hunion₁ :
            (ERLarge ∪ ERMedium ∪ ERSmall).card ≤
              (ERLarge ∪ ERMedium).card + ERSmall.card :=
          Finset.card_union_le (ERLarge ∪ ERMedium) ERSmall
        have hunion₂ :
            (ERLarge ∪ ERMedium).card ≤ ERLarge.card + ERMedium.card :=
          Finset.card_union_le ERLarge ERMedium
        omega
      have hRedClass_card_le_closed :
          ∀ (clsFirst clsOmega : TwoBiteBaseVertex m → Prop),
            (∀ b : Fin m, clsFirst (Sum.inr b) → clsOmega (Sum.inr b)) →
              (terminal.filter (redFirstClassExceptional clsFirst)).card ≤
                (TwoBiteClosedPairsInClass ω I clsOmega).card := by
        intro clsFirst clsOmega hclsTransfer
        let S : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
          terminal.filter (redFirstClassExceptional clsFirst)
        let Fcls : Finset (Fin n × Fin n) :=
          TwoBiteClosedPairsInClass ω I clsOmega
        let redPairOfFinal : Fin n × Fin n →
            Sum (Fin m × Fin m) (Fin m × Fin m) :=
          fun a =>
            if (TwoBiteRedProjection ω a.1).val <
                (TwoBiteRedProjection ω a.2).val then
              Sum.inl (TwoBiteRedProjection ω a.1,
                TwoBiteRedProjection ω a.2)
            else
              Sum.inl (TwoBiteRedProjection ω a.2,
                TwoBiteRedProjection ω a.1)
        have hsubset : S ⊆ Fcls.image redPairOfFinal := by
          intro e he
          have hpred : redFirstClassExceptional clsFirst e :=
            (Finset.mem_filter.mp he).2
          cases e with
          | inl q =>
              dsimp [redFirstClassExceptional] at hpred
              rcases hpred with ⟨b, hbclsFirst, hqFirst⟩
              have hbCoverage := hBlueCoverage b
              have hbclsOmega : clsOmega (Sum.inr b) :=
                hclsTransfer b hbclsFirst
              have hqω :
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inr b)).image
                        (TwoBiteRedProjection ω)) :=
                (hbCoverage.2.2.2.2 q).2 hqFirst
              rcases hProjectedPair_has_final_pair (TwoBiteRedProjection ω)
                  (TwoBiteX ω I (Sum.inr b)) q hqω with
                ⟨a, haFinal, hproj⟩
              have haClosed : a ∈ Fcls := by
                dsimp [Fcls, TwoBiteClosedPairsInClass]
                rw [Finset.mem_biUnion]
                exact ⟨Sum.inr b, by simp [hbclsOmega], haFinal⟩
              rw [Finset.mem_image]
              refine ⟨a, haClosed, ?_⟩
              have hqrank : q.1.val < q.2.val := by
                have hq' := hqω
                simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq'
                exact hq'.2
              rcases hproj with hdir | hrev
              · have hif :
                    (TwoBiteRedProjection ω a.1).val <
                      (TwoBiteRedProjection ω a.2).val := by
                  simpa [hdir.1, hdir.2] using hqrank
                change
                  (if (TwoBiteRedProjection ω a.1).val <
                        (TwoBiteRedProjection ω a.2).val then
                      Sum.inl (TwoBiteRedProjection ω a.1,
                        TwoBiteRedProjection ω a.2)
                    else
                      Sum.inl (TwoBiteRedProjection ω a.2,
                        TwoBiteRedProjection ω a.1)) = Sum.inl q
                rw [if_pos hif]
                simp [hdir.1, hdir.2]
              · have hif :
                    ¬ (TwoBiteRedProjection ω a.1).val <
                      (TwoBiteRedProjection ω a.2).val := by
                  have hnot : ¬ q.2.val < q.1.val :=
                    not_lt.mpr (le_of_lt hqrank)
                  simpa [hrev.1, hrev.2] using hnot
                change
                  (if (TwoBiteRedProjection ω a.1).val <
                        (TwoBiteRedProjection ω a.2).val then
                      Sum.inl (TwoBiteRedProjection ω a.1,
                        TwoBiteRedProjection ω a.2)
                    else
                      Sum.inl (TwoBiteRedProjection ω a.2,
                        TwoBiteRedProjection ω a.1)) = Sum.inl q
                rw [if_neg hif]
                simp [hrev.1, hrev.2]
          | inr q =>
              dsimp [redFirstClassExceptional] at hpred
        have hcard_subset : S.card ≤ (Fcls.image redPairOfFinal).card :=
          Finset.card_le_card hsubset
        have himage_card : (Fcls.image redPairOfFinal).card ≤ Fcls.card :=
          Finset.card_image_le
        simpa [S, Fcls] using le_trans hcard_subset himage_card
      have hER_count_by_classes :
          (ER.card : ℝ) ≤
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ) +
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) +
                ((TwoBiteClosedPairsInClass ω I
                  (TwoBiteSmallClass ω ε I)).card : ℝ) := by
        have hclassCover :
            (ER.card : ℝ) ≤
              (ERLarge.card : ℝ) + (ERMedium.card : ℝ) +
                (ERSmall.card : ℝ) := by
          exact_mod_cast hER_card_le_class_union
        have hLarge :
            (ERLarge.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteLargeClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [ERLarge] using
                hRedClass_card_le_closed
                  (TwoBiteLargeClass ωFirst ε I)
                  (TwoBiteLargeClass ω ε I)
                  (fun b hb =>
                    ((hBlueCoverage b).2.1).2 hb))
        have hMedium :
            (ERMedium.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [ERMedium] using
                hRedClass_card_le_closed
                  (TwoBiteMediumClass ωFirst ε I)
                  (TwoBiteMediumClass ω ε I)
                  (fun b hb =>
                    ((hBlueCoverage b).2.2.1).2 hb))
        have hSmall :
            (ERSmall.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteSmallClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [ERSmall] using
                hRedClass_card_le_closed
                  (TwoBiteSmallClass ωFirst ε I)
                  (TwoBiteSmallClass ω ε I)
                  (fun b hb =>
                    ((hBlueCoverage b).2.2.2.1).2 hb))
        nlinarith
      dsimp [ClosedPairsBound]
      exact le_trans hER_count_by_classes hTripleClosedBound
    · intro e heOpen hePresent hRedTag hIndep
      have hterm : e ∈ terminal := hStagedTerminal ω hω e heOpen
      have hCoverage :=
        FixedSetOppositeColorTerminalCoverage (I := I)
          (recorded := recorded) (terminal := terminal)
          (ω := ω) (ωFirst := ωFirst)
          hEmb hRecordedAgree (hRecorded ω hω)
          (hRecorded ωFirst hHistFirst) hTerminal
      have hBlueCoverage := hCoverage.1 hBlueTerminal
      have hClassifyAll :=
        FixedSetExceptionalWitnessClassification (n := n) (m := m) (k := k)
          (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0)
          ω I hε1_nonneg hComparisons hn hm hpClass hIcard hk
          hRegularity
      rcases hClassifyAll with
        ⟨_ERω, _EBω, _hERω, _hEBω, hClassify, _hERBound, _hEBBound⟩
      cases e with
      | inl q =>
          have hpresentRed : (TwoBiteRedGraph ω).Adj q.1 q.2 := by
            simpa [TwoBiteEdgeCoordinateValue] using hePresent
          have hClassified := hClassify (Sum.inl q) heOpen hpresentRed hIndep
          have hRedExceptionalω :
              ∃ b : Fin m,
                (TwoBiteLargeClass ω ε I (Sum.inr b) ∨
                  TwoBiteMediumClass ω ε I (Sum.inr b) ∨
                    TwoBiteSmallClass ω ε I (Sum.inr b)) ∧
                q ∈
                  TwoBiteBasePairs
                    ((TwoBiteX ω I (Sum.inr b)).image
                      (TwoBiteRedProjection ω)) := by
            simpa using hClassified
          rcases hRedExceptionalω with ⟨b, hbClass, hq⟩
          have hbCoverage := hBlueCoverage b
          have hbLargeIff :
              TwoBiteLargeClass ω ε I (Sum.inr b) ↔
                TwoBiteLargeClass ωFirst ε I (Sum.inr b) :=
            hbCoverage.2.1
          have hbMediumIff :
              TwoBiteMediumClass ω ε I (Sum.inr b) ↔
                TwoBiteMediumClass ωFirst ε I (Sum.inr b) :=
            hbCoverage.2.2.1
          have hbSmallIff :
              TwoBiteSmallClass ω ε I (Sum.inr b) ↔
                TwoBiteSmallClass ωFirst ε I (Sum.inr b) :=
            hbCoverage.2.2.2.1
          have hbClassFirst :
              TwoBiteLargeClass ωFirst ε I (Sum.inr b) ∨
                TwoBiteMediumClass ωFirst ε I (Sum.inr b) ∨
                  TwoBiteSmallClass ωFirst ε I (Sum.inr b) := by
            rcases hbClass with hbLarge | hbRest
            · exact Or.inl (hbLargeIff.1 hbLarge)
            · rcases hbRest with hbMedium | hbSmall
              · exact Or.inr (Or.inl (hbMediumIff.1 hbMedium))
              · exact Or.inr (Or.inr (hbSmallIff.1 hbSmall))
          have hqFirst :
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ωFirst I (Sum.inr b)).image
                    (TwoBiteRedProjection ωFirst)) :=
            (hbCoverage.2.2.2.2 q).1 hq
          have hredFirst : redExceptional (Sum.inl q) :=
            ⟨b, hbClassFirst, hqFirst⟩
          simpa [ER] using
            (Finset.mem_filter.mpr ⟨hterm, hredFirst⟩ :
              Sum.inl q ∈ terminal.filter redExceptional)
      | inr q =>
          cases hRedTag
  · intro ω hω hEmb hRecordedAgree hRedTerminal hRegularity
    constructor
    · have hCoverage :=
        FixedSetOppositeColorTerminalCoverage (I := I)
          (recorded := recorded) (terminal := terminal)
          (ω := ω) (ωFirst := ωFirst)
          hEmb hRecordedAgree (hRecorded ω hω)
          (hRecorded ωFirst hHistFirst) hTerminal
      have hRedCoverage := hCoverage.2 hRedTerminal
      have hFiber : FiberAndDegreeEvent ω ε2 := by
        simpa [TwoBiteRegularityEvent] using hRegularity.1
      have hMediumEvent :
          TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω := by
        simpa [TwoBiteRegularityEvent] using hRegularity.2.1
      have hSmallEvent :
          TwoBiteSmallClosedPairsEvent (k := k) ε ε1 ω := by
        simpa [TwoBiteRegularityEvent] using hRegularity.2.2
      have hI_scale :
          I.card = TwoBiteNaturalIndependenceScale (1 + ε) n := by
        rw [hIcard, hk]
      have hLargeClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) := by
        have h := LargeClosedPairsBound ω I hComparisons hn hI_scale hFiber
        simpa [hIcard] using h
      have hMediumClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteMediumClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) :=
        hMediumEvent I hIcard
      have hSmallClosed :
          ClosedPairsBound
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteSmallClass ω ε I)).card : ℝ)
            ε1 (k : ℝ) :=
        hSmallEvent I hIcard
      have hTripleClosedBound :
          ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ) +
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) +
                ((TwoBiteClosedPairsInClass ω I
                  (TwoBiteSmallClass ω ε I)).card : ℝ)
            ≤ (3 * ε1) * (k : ℝ) ^ 2 := by
        dsimp [ClosedPairsBound] at hLargeClosed hMediumClosed hSmallClosed
        nlinarith
      let blueFirstClassExceptional (cls : TwoBiteBaseVertex m → Prop) :
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
        fun e =>
          match e with
          | Sum.inl _ => False
          | Sum.inr q =>
              ∃ r : Fin m,
                cls (Sum.inl r) ∧
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ωFirst I (Sum.inl r)).image
                        (TwoBiteBlueProjection ωFirst))
      let EBLarge : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (blueFirstClassExceptional (TwoBiteLargeClass ωFirst ε I))
      let EBMedium : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (blueFirstClassExceptional (TwoBiteMediumClass ωFirst ε I))
      let EBSmall : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
        terminal.filter
          (blueFirstClassExceptional (TwoBiteSmallClass ωFirst ε I))
      have hBlueExceptional_cases :
          ∀ e, blueExceptional e →
            blueFirstClassExceptional (TwoBiteLargeClass ωFirst ε I) e ∨
              blueFirstClassExceptional (TwoBiteMediumClass ωFirst ε I) e ∨
                blueFirstClassExceptional (TwoBiteSmallClass ωFirst ε I) e := by
        intro e he
        cases e with
        | inl q =>
            dsimp [blueExceptional] at he
        | inr q =>
            dsimp [blueExceptional, blueFirstClassExceptional] at he ⊢
            rcases he with ⟨r, hrClass, hq⟩
            rcases hrClass with hrLarge | hrRest
            · exact Or.inl ⟨r, hrLarge, hq⟩
            · rcases hrRest with hrMedium | hrSmall
              · exact Or.inr (Or.inl ⟨r, hrMedium, hq⟩)
              · exact Or.inr (Or.inr ⟨r, hrSmall, hq⟩)
      have hEB_subset_class_union :
          EB ⊆ EBLarge ∪ EBMedium ∪ EBSmall := by
        intro e he
        have hpack : e ∈ terminal ∧ blueExceptional e := by
          simpa [EB] using (Finset.mem_filter.mp he)
        have hterm : e ∈ terminal := hpack.1
        have hblue : blueExceptional e := hpack.2
        rcases hBlueExceptional_cases e hblue with hlarge | hrest
        · simp [EBLarge, hterm, hlarge]
        · rcases hrest with hmedium | hsmall
          · simp [EBMedium, hterm, hmedium]
          · simp [EBSmall, hterm, hsmall]
      have hEB_card_le_class_union :
          EB.card ≤ EBLarge.card + EBMedium.card + EBSmall.card := by
        have hsub :
            EB.card ≤ (EBLarge ∪ EBMedium ∪ EBSmall).card :=
          Finset.card_le_card hEB_subset_class_union
        have hunion₁ :
            (EBLarge ∪ EBMedium ∪ EBSmall).card ≤
              (EBLarge ∪ EBMedium).card + EBSmall.card :=
          Finset.card_union_le (EBLarge ∪ EBMedium) EBSmall
        have hunion₂ :
            (EBLarge ∪ EBMedium).card ≤ EBLarge.card + EBMedium.card :=
          Finset.card_union_le EBLarge EBMedium
        omega
      have hBlueClass_card_le_closed :
          ∀ (clsFirst clsOmega : TwoBiteBaseVertex m → Prop),
            (∀ r : Fin m, clsFirst (Sum.inl r) → clsOmega (Sum.inl r)) →
              (terminal.filter (blueFirstClassExceptional clsFirst)).card ≤
                (TwoBiteClosedPairsInClass ω I clsOmega).card := by
        intro clsFirst clsOmega hclsTransfer
        let S : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
          terminal.filter (blueFirstClassExceptional clsFirst)
        let Fcls : Finset (Fin n × Fin n) :=
          TwoBiteClosedPairsInClass ω I clsOmega
        let bluePairOfFinal : Fin n × Fin n →
            Sum (Fin m × Fin m) (Fin m × Fin m) :=
          fun a =>
            if (TwoBiteBlueProjection ω a.1).val <
                (TwoBiteBlueProjection ω a.2).val then
              Sum.inr (TwoBiteBlueProjection ω a.1,
                TwoBiteBlueProjection ω a.2)
            else
              Sum.inr (TwoBiteBlueProjection ω a.2,
                TwoBiteBlueProjection ω a.1)
        have hsubset : S ⊆ Fcls.image bluePairOfFinal := by
          intro e he
          have hpred : blueFirstClassExceptional clsFirst e :=
            (Finset.mem_filter.mp he).2
          cases e with
          | inl q =>
              dsimp [blueFirstClassExceptional] at hpred
          | inr q =>
              dsimp [blueFirstClassExceptional] at hpred
              rcases hpred with ⟨r, hrclsFirst, hqFirst⟩
              have hrCoverage := hRedCoverage r
              have hrclsOmega : clsOmega (Sum.inl r) :=
                hclsTransfer r hrclsFirst
              have hqω :
                  q ∈
                    TwoBiteBasePairs
                      ((TwoBiteX ω I (Sum.inl r)).image
                        (TwoBiteBlueProjection ω)) :=
                (hrCoverage.2.2.2.2 q).2 hqFirst
              rcases hProjectedPair_has_final_pair (TwoBiteBlueProjection ω)
                  (TwoBiteX ω I (Sum.inl r)) q hqω with
                ⟨a, haFinal, hproj⟩
              have haClosed : a ∈ Fcls := by
                dsimp [Fcls, TwoBiteClosedPairsInClass]
                rw [Finset.mem_biUnion]
                exact ⟨Sum.inl r, by simp [hrclsOmega], haFinal⟩
              rw [Finset.mem_image]
              refine ⟨a, haClosed, ?_⟩
              have hqrank : q.1.val < q.2.val := by
                have hq' := hqω
                simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq'
                exact hq'.2
              rcases hproj with hdir | hrev
              · have hif :
                    (TwoBiteBlueProjection ω a.1).val <
                      (TwoBiteBlueProjection ω a.2).val := by
                  simpa [hdir.1, hdir.2] using hqrank
                change
                  (if (TwoBiteBlueProjection ω a.1).val <
                        (TwoBiteBlueProjection ω a.2).val then
                      Sum.inr (TwoBiteBlueProjection ω a.1,
                        TwoBiteBlueProjection ω a.2)
                    else
                      Sum.inr (TwoBiteBlueProjection ω a.2,
                        TwoBiteBlueProjection ω a.1)) = Sum.inr q
                rw [if_pos hif]
                simp [hdir.1, hdir.2]
              · have hif :
                    ¬ (TwoBiteBlueProjection ω a.1).val <
                      (TwoBiteBlueProjection ω a.2).val := by
                  have hnot : ¬ q.2.val < q.1.val :=
                    not_lt.mpr (le_of_lt hqrank)
                  simpa [hrev.1, hrev.2] using hnot
                change
                  (if (TwoBiteBlueProjection ω a.1).val <
                        (TwoBiteBlueProjection ω a.2).val then
                      Sum.inr (TwoBiteBlueProjection ω a.1,
                        TwoBiteBlueProjection ω a.2)
                    else
                      Sum.inr (TwoBiteBlueProjection ω a.2,
                        TwoBiteBlueProjection ω a.1)) = Sum.inr q
                rw [if_neg hif]
                simp [hrev.1, hrev.2]
        have hcard_subset : S.card ≤ (Fcls.image bluePairOfFinal).card :=
          Finset.card_le_card hsubset
        have himage_card : (Fcls.image bluePairOfFinal).card ≤ Fcls.card :=
          Finset.card_image_le
        simpa [S, Fcls] using le_trans hcard_subset himage_card
      have hEB_count_by_classes :
          (EB.card : ℝ) ≤
            ((TwoBiteClosedPairsInClass ω I
              (TwoBiteLargeClass ω ε I)).card : ℝ) +
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) +
                ((TwoBiteClosedPairsInClass ω I
                  (TwoBiteSmallClass ω ε I)).card : ℝ) := by
        have hclassCover :
            (EB.card : ℝ) ≤
              (EBLarge.card : ℝ) + (EBMedium.card : ℝ) +
                (EBSmall.card : ℝ) := by
          exact_mod_cast hEB_card_le_class_union
        have hLarge :
            (EBLarge.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteLargeClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [EBLarge] using
                hBlueClass_card_le_closed
                  (TwoBiteLargeClass ωFirst ε I)
                  (TwoBiteLargeClass ω ε I)
                  (fun r hr =>
                    ((hRedCoverage r).2.1).2 hr))
        have hMedium :
            (EBMedium.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteMediumClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [EBMedium] using
                hBlueClass_card_le_closed
                  (TwoBiteMediumClass ωFirst ε I)
                  (TwoBiteMediumClass ω ε I)
                  (fun r hr =>
                    ((hRedCoverage r).2.2.1).2 hr))
        have hSmall :
            (EBSmall.card : ℝ) ≤
              ((TwoBiteClosedPairsInClass ω I
                (TwoBiteSmallClass ω ε I)).card : ℝ) := by
          exact_mod_cast
            (by
              simpa [EBSmall] using
                hBlueClass_card_le_closed
                  (TwoBiteSmallClass ωFirst ε I)
                  (TwoBiteSmallClass ω ε I)
                  (fun r hr =>
                    ((hRedCoverage r).2.2.2.1).2 hr))
        nlinarith
      dsimp [ClosedPairsBound]
      exact le_trans hEB_count_by_classes hTripleClosedBound
    · intro e heOpen hePresent hBlueTag hIndep
      have hterm : e ∈ terminal := hStagedTerminal ω hω e heOpen
      have hCoverage :=
        FixedSetOppositeColorTerminalCoverage (I := I)
          (recorded := recorded) (terminal := terminal)
          (ω := ω) (ωFirst := ωFirst)
          hEmb hRecordedAgree (hRecorded ω hω)
          (hRecorded ωFirst hHistFirst) hTerminal
      have hRedCoverage := hCoverage.2 hRedTerminal
      have hClassifyAll :=
        FixedSetExceptionalWitnessClassification (n := n) (m := m) (k := k)
          (p := p) (ε := ε) (ε1 := ε1) (ε2 := ε2) (n0 := n0)
          ω I hε1_nonneg hComparisons hn hm hpClass hIcard hk
          hRegularity
      rcases hClassifyAll with
        ⟨_ERω, _EBω, _hERω, _hEBω, hClassify, _hERBound, _hEBBound⟩
      cases e with
      | inl q =>
          cases hBlueTag
      | inr q =>
          have hpresentBlue : (TwoBiteBlueGraph ω).Adj q.1 q.2 := by
            simpa [TwoBiteEdgeCoordinateValue] using hePresent
          have hClassified := hClassify (Sum.inr q) heOpen hpresentBlue hIndep
          have hBlueExceptionalω :
              ∃ r : Fin m,
                (TwoBiteLargeClass ω ε I (Sum.inl r) ∨
                  TwoBiteMediumClass ω ε I (Sum.inl r) ∨
                    TwoBiteSmallClass ω ε I (Sum.inl r)) ∧
                q ∈
                  TwoBiteBasePairs
                    ((TwoBiteX ω I (Sum.inl r)).image
                      (TwoBiteBlueProjection ω)) := by
            simpa using hClassified
          rcases hBlueExceptionalω with ⟨r, hrClass, hq⟩
          have hrCoverage := hRedCoverage r
          have hrLargeIff :
              TwoBiteLargeClass ω ε I (Sum.inl r) ↔
                TwoBiteLargeClass ωFirst ε I (Sum.inl r) :=
            hrCoverage.2.1
          have hrMediumIff :
              TwoBiteMediumClass ω ε I (Sum.inl r) ↔
                TwoBiteMediumClass ωFirst ε I (Sum.inl r) :=
            hrCoverage.2.2.1
          have hrSmallIff :
              TwoBiteSmallClass ω ε I (Sum.inl r) ↔
                TwoBiteSmallClass ωFirst ε I (Sum.inl r) :=
            hrCoverage.2.2.2.1
          have hrClassFirst :
              TwoBiteLargeClass ωFirst ε I (Sum.inl r) ∨
                TwoBiteMediumClass ωFirst ε I (Sum.inl r) ∨
                  TwoBiteSmallClass ωFirst ε I (Sum.inl r) := by
            rcases hrClass with hrLarge | hrRest
            · exact Or.inl (hrLargeIff.1 hrLarge)
            · rcases hrRest with hrMedium | hrSmall
              · exact Or.inr (Or.inl (hrMediumIff.1 hrMedium))
              · exact Or.inr (Or.inr (hrSmallIff.1 hrSmall))
          have hqFirst :
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteX ωFirst I (Sum.inl r)).image
                    (TwoBiteBlueProjection ωFirst)) :=
            (hrCoverage.2.2.2.2 q).1 hq
          have hblueFirst : blueExceptional (Sum.inr q) :=
            ⟨r, hrClassFirst, hqFirst⟩
          simpa [EB] using
            (Finset.mem_filter.mpr ⟨hterm, hblueFirst⟩ :
              Sum.inr q ∈ terminal.filter blueExceptional)
