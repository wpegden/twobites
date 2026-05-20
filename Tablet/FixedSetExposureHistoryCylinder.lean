import Tablet.FixedSetPreTerminalHistoryPartition
import Tablet.FixedSetTerminalSupportClassification
import Tablet.FixedSetSameColorClosedWitnessCylinder
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteStageRevealedVertex
import Tablet.TwoBiteTerminalCoordinateUniverse
import Tablet.TwoBitePreTerminalRecordedPairs

-- [TABLET NODE: FixedSetExposureHistoryCylinder]

theorem FixedSetExposureHistoryCylinder :
    ∀ {n m k ℓR ℓB : ℕ} {p ε : ℝ} (I : Finset (Fin n)),
      ∃ ι : Type, ∃ _ : Fintype ι,
        ∃ hist : ι → TwoBiteSample n m p → Prop,
          ∃ recorded :
            ι → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∃ terminal :
              ι → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∃ order :
              ι → List (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∃ rep : ι → TwoBiteSample n m p,
            (∀ ω : TwoBiteSample n m p,
              TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                (ℓB := ℓB) ω I ↔ ∃ i : ι, hist i ω) ∧
            (∀ i j : ι, i ≠ j → ∀ ω : TwoBiteSample n m p,
              ¬ (hist i ω ∧ hist j ω)) ∧
            (∀ i : ι, hist i (rep i)) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω ↔
                (∀ x : Fin n, ω.2.2 x = (rep i).2.2 x) ∧
                (∀ e,
                  e ∈ recorded i →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue (rep i) e))) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ recorded i) ∧
            (∀ i : ι, ∀ e,
              e ∈ recorded i →
                match e with
                | Sum.inl q => q.1.val < q.2.val
                | Sum.inr q => q.1.val < q.2.val) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                  (ℓB := ℓB) ω I) ∧
            (∀ i : ι,
              (order i).Nodup ∧ (order i).toFinset = terminal i) ∧
            (∀ i : ι, ∀ e,
              e ∈ terminal i ↔
                e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded i) ∧
            (∀ i : ι, ∀ e,
              e ∈ terminal i → e ∉ recorded i) ∧
            (∀ i : ι, ∀ e,
              e ∈ terminal i →
                match e with
                | Sum.inl q => q.1.val < q.2.val
                | Sum.inr q => q.1.val < q.2.val) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                    e ∈ terminal i) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
                  (e : Sum (Fin m × Fin m) (Fin m × Fin m))
                  (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
                  order i = pre ++ e :: suffix →
                    ∀ ω' : TwoBiteSample n m p,
                      (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                      (∀ c,
                        c ∈ recorded i →
                          (TwoBiteEdgeCoordinateValue ω c ↔
                            TwoBiteEdgeCoordinateValue ω' c)) →
                      (∀ c,
                        c ∈ pre.toFinset →
                          (TwoBiteEdgeCoordinateValue ω c ↔
                            TwoBiteEdgeCoordinateValue ω' c)) →
                        (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                          e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                        (TwoBiteProjectionPairTouched ω ε I e ↔
                          TwoBiteProjectionPairTouched ω' ε I e) ∧
                        (TwoBiteProjectionPairSameColorClosed ω I e ↔
                          TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                        (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                          e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε I
  rcases FixedSetPreTerminalHistoryPartition
      (m := m) (k := k) (ℓR := ℓR) (ℓB := ℓB)
      (p := p) (ε := ε) I with
    ⟨ι, instι, hist, recorded, rep, hcover, hdisjoint, hrep,
      hcylinder, hrecorded, hevent, hreplay, hstaged⟩
  let terminal : ι → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    fun i => Classical.choose (FixedSetTerminalSupportClassification (recorded i))
  let order : ι → List (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    fun i =>
      Classical.choose
        (Classical.choose_spec
          (FixedSetTerminalSupportClassification (recorded i)))
  have hterminalData :
      ∀ i,
        (∀ e, e ∈ terminal i ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded i) ∧
        (order i).Nodup ∧
        (order i).toFinset = terminal i ∧
        (∀ e, e ∈ terminal i → e ∉ recorded i) ∧
        (∀ e, e ∈ terminal i →
          match e with
          | Sum.inl q => q.1.val < q.2.val
          | Sum.inr q => q.1.val < q.2.val) ∧
        (∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (e : Sum (Fin m × Fin m) (Fin m × Fin m))
          (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
          order i = pre ++ e :: suffix →
            match e with
            | Sum.inl q =>
                ∀ r : Fin m,
                  r.val < q.1.val →
                  r.val < q.2.val →
                    Sum.inl (r, q.1) ∈ recorded i ∪ pre.toFinset ∧
                      Sum.inl (r, q.2) ∈ recorded i ∪ pre.toFinset
            | Sum.inr q =>
                ∀ b : Fin m,
                  b.val < q.1.val →
                  b.val < q.2.val →
                    Sum.inr (b, q.1) ∈ recorded i ∪ pre.toFinset ∧
                      Sum.inr (b, q.2) ∈ recorded i ∪ pre.toFinset) := by
    intro i
    exact
      Classical.choose_spec
        (Classical.choose_spec
          (FixedSetTerminalSupportClassification (recorded i)))
  have hterminalIff :
      ∀ i, ∀ e,
        e ∈ terminal i ↔
          e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded i := by
    intro i
    exact (hterminalData i).1
  have horderFacts :
      ∀ i, (order i).Nodup ∧ (order i).toFinset = terminal i := by
    intro i
    exact ⟨(hterminalData i).2.1, (hterminalData i).2.2.1⟩
  have hterminalUnrecorded :
      ∀ i, ∀ e, e ∈ terminal i → e ∉ recorded i := by
    intro i
    exact (hterminalData i).2.2.2.1
  have hterminalOriented :
      ∀ i, ∀ e,
        e ∈ terminal i →
          match e with
          | Sum.inl q => q.1.val < q.2.val
          | Sum.inr q => q.1.val < q.2.val := by
    intro i
    exact (hterminalData i).2.2.2.2.1
  have hsupport :
      ∀ i,
        ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (e : Sum (Fin m × Fin m) (Fin m × Fin m))
          (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
          order i = pre ++ e :: suffix →
            match e with
            | Sum.inl q =>
                ∀ r : Fin m,
                  r.val < q.1.val →
                  r.val < q.2.val →
                    Sum.inl (r, q.1) ∈ recorded i ∪ pre.toFinset ∧
                      Sum.inl (r, q.2) ∈ recorded i ∪ pre.toFinset
            | Sum.inr q =>
                ∀ b : Fin m,
                  b.val < q.1.val →
                  b.val < q.2.val →
                    Sum.inr (b, q.1) ∈ recorded i ∪ pre.toFinset ∧
                      Sum.inr (b, q.2) ∈ recorded i ∪ pre.toFinset := by
    intro i
    exact (hterminalData i).2.2.2.2.2
  refine
    ⟨ι, instι, hist, recorded, terminal, order, rep, hcover, hdisjoint,
      hrep, hcylinder, hrecorded, ?_, hevent, horderFacts, hterminalIff,
      hterminalUnrecorded, hterminalOriented, ?_, ?_⟩
  · intro i e he
    have hpre :
        e ∈ TwoBitePreTerminalRecordedPairs (rep i) ε I :=
      (hrecorded i (rep i) (hrep i) e).2 he
    have hterminalUniverse :
        e ∈ TwoBiteTerminalCoordinateUniverse m := by
      unfold TwoBitePreTerminalRecordedPairs at hpre
      exact (Finset.mem_filter.mp hpre).1
    cases e <;> simpa [TwoBiteTerminalCoordinateUniverse] using hterminalUniverse
  · intro i ω hhist e hopen
    exact (hterminalIff i e).2 (hstaged i ω hhist e hopen)
  · intro i ω hhist pre e suffix horder ω' hEmbedding hAgreeRecorded
      hAgreePrefix
    have hreplayData := hreplay i ω hhist ω' hEmbedding hAgreeRecorded
    have hstage :
        ∀ x,
          TwoBiteStageRevealedVertex ω ε I x ↔
            TwoBiteStageRevealedVertex ω' ε I x :=
      hreplayData.1
    have htouched :
        ∀ e,
          TwoBiteProjectionPairTouched ω ε I e ↔
            TwoBiteProjectionPairTouched ω' ε I e :=
      hreplayData.2
    have hhist' : hist i ω' := by
      have hcell := (hcylinder i ω).1 hhist
      refine (hcylinder i ω').2 ⟨?_, ?_⟩
      · intro x
        exact (hEmbedding x).symm.trans (hcell.1 x)
      · intro c hc
        have hωrep := hcell.2 c hc
        have hωω' := hAgreeRecorded c hc
        constructor
        · intro hω'
          exact hωrep.1 (hωω'.2 hω')
        · intro hrepVal
          exact hωω'.1 (hωrep.2 hrepVal)
    have hpreterminal :
        e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
          e ∈ TwoBitePreTerminalRecordedPairs ω' ε I := by
      exact
        (hrecorded i ω hhist e).trans
          ((hrecorded i ω' hhist' e).symm)
    have hagreeSupport :
        ∀ c,
          c ∈ recorded i ∪ pre.toFinset →
            (TwoBiteEdgeCoordinateValue ω c ↔
              TwoBiteEdgeCoordinateValue ω' c) := by
      intro c hc
      rcases Finset.mem_union.mp hc with hrec | hpre
      · exact hAgreeRecorded c hrec
      · exact hAgreePrefix c hpre
    have hsame :
        TwoBiteProjectionPairSameColorClosed ω I e ↔
          TwoBiteProjectionPairSameColorClosed ω' I e :=
      FixedSetSameColorClosedWitnessCylinder ω ω' I e
        (recorded i ∪ pre.toFinset) hEmbedding hagreeSupport
        (hsupport i pre e suffix horder)
    have hpairset :
        e ∈ TwoBiteProjectionPairSet ω I ↔
          e ∈ TwoBiteProjectionPairSet ω' I := by
      simp [TwoBiteProjectionPairSet, TwoBiteBasePairs, TwoBitePairsInSet,
        TwoBiteRedProjection, TwoBiteBlueProjection, TwoBiteEmbedding,
        hEmbedding]
    have hstagedOpen :
        e ∈ TwoBiteStagedOpenPairs ω ε I ↔
          e ∈ TwoBiteStagedOpenPairs ω' ε I := by
      unfold TwoBiteStagedOpenPairs
      simp [hpairset, hsame, htouched e, hpreterminal]
    exact ⟨hstagedOpen, htouched e, hsame, hpreterminal⟩
