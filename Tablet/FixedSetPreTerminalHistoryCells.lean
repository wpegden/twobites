import Tablet.FixedSetPreTerminalReplayTranscriptConstruction
import Tablet.FixedSetPreTerminalF2QueriesRecorded
import Tablet.FixedSetPreTerminalRecordedPairsReplayEquality
import Tablet.FixedSetPreTerminalReplayUniqueness
import Tablet.FixedSetPreTerminalStageTouchPreservation
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStageRevealedVertex

-- [TABLET NODE: FixedSetPreTerminalHistoryCells]

theorem FixedSetPreTerminalHistoryCells :
    ∀ {n m k ℓR ℓB : ℕ} {p ε : ℝ} (I : Finset (Fin n)),
      ∃ ι : Type, ∃ _ : Fintype ι,
        ∃ hist : ι → TwoBiteSample n m p → Prop,
          ∃ recorded :
            ι → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
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
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
                  (ℓB := ℓB) ω I) ∧
            (∀ i : ι, ∀ ω : TwoBiteSample n m p,
              hist i ω →
                ∀ ω' : TwoBiteSample n m p,
                  (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                  (∀ c,
                    c ∈ recorded i →
                      (TwoBiteEdgeCoordinateValue ω c ↔
                        TwoBiteEdgeCoordinateValue ω' c)) →
                    (∀ x,
                      TwoBiteStageRevealedVertex ω ε I x ↔
                        TwoBiteStageRevealedVertex ω' ε I x) ∧
                    (∀ e,
                      TwoBiteProjectionPairTouched ω ε I e ↔
                        TwoBiteProjectionPairTouched ω' ε I e)) := by
-- BODY
  intro n m k ℓR ℓB p ε I
  classical
  let C := Sum (Fin m × Fin m) (Fin m × Fin m)
  let edgeRecord : TwoBiteSample n m p → Finset C :=
    fun ω => (TwoBitePreTerminalRecordedPairs ω ε I).filter
      (fun e => TwoBiteEdgeCoordinateValue ω e)
  let Transcript :=
    (Fin n ↪ (Fin m × Fin m)) × Finset C × Finset C
  let transcript : TwoBiteSample n m p → Transcript :=
    fun ω => (ω.2.2, TwoBitePreTerminalRecordedPairs ω ε I, edgeRecord ω)
  let ι : Type :=
    {t : Transcript //
      ∃ ω : TwoBiteSample n m p,
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I ∧ transcript ω = t}
  let rep : ι → TwoBiteSample n m p := fun i => Classical.choose i.2
  let recorded : ι → Finset C := fun i => i.1.2.1
  let hist : ι → TwoBiteSample n m p → Prop :=
    fun i ω =>
      (∀ x : Fin n, ω.2.2 x = (rep i).2.2 x) ∧
        (∀ e,
          e ∈ recorded i →
            (TwoBiteEdgeCoordinateValue ω e ↔
              TwoBiteEdgeCoordinateValue (rep i) e))
  have hRepSpec :
      ∀ i : ι,
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) (rep i) I ∧ transcript (rep i) = i.1 := by
    intro i
    exact Classical.choose_spec i.2
  have hRepRecorded :
      ∀ i : ι, ∀ e,
        e ∈ TwoBitePreTerminalRecordedPairs (rep i) ε I ↔
          e ∈ recorded i := by
    intro i e
    have hrec :
        TwoBitePreTerminalRecordedPairs (rep i) ε I = recorded i := by
      simpa [transcript, recorded] using
        congrArg (fun t : Transcript => t.2.1) (hRepSpec i).2
    simp [hrec]
  have hHistFromTranscript :
      ∀ i : ι, ∀ ω : TwoBiteSample n m p,
        transcript (rep i) = transcript ω → hist i ω := by
    intro i ω ht
    constructor
    · intro x
      have hEmb :
          (rep i).2.2 = ω.2.2 := by
        simpa [transcript] using
          congrArg (fun t : Transcript => t.1) ht
      exact (congrArg (fun f : Fin n ↪ (Fin m × Fin m) => f x) hEmb).symm
    · intro e he
      have hRepMem :
          e ∈ TwoBitePreTerminalRecordedPairs (rep i) ε I :=
        (hRepRecorded i e).2 he
      have hOmegaMem :
          e ∈ TwoBitePreTerminalRecordedPairs ω ε I := by
        have hrec :
            TwoBitePreTerminalRecordedPairs (rep i) ε I =
              TwoBitePreTerminalRecordedPairs ω ε I := by
          simpa [transcript] using
            congrArg (fun t : Transcript => t.2.1) ht
        simpa [hrec] using hRepMem
      have hEdgeSet :
          edgeRecord (rep i) = edgeRecord ω := by
        simpa [transcript] using
          congrArg (fun t : Transcript => t.2.2) ht
      have hmemiff :
          e ∈ edgeRecord (rep i) ↔ e ∈ edgeRecord ω := by
        rw [hEdgeSet]
      have hrep :
          e ∈ edgeRecord (rep i) ↔
            TwoBiteEdgeCoordinateValue (rep i) e := by
        simp [edgeRecord, hRepMem]
      have homega :
          e ∈ edgeRecord ω ↔ TwoBiteEdgeCoordinateValue ω e := by
        simp [edgeRecord, hOmegaMem]
      constructor
      · intro hω
        exact hrep.1 (hmemiff.2 (homega.2 hω))
      · intro hrepEdge
        exact homega.1 (hmemiff.1 (hrep.2 hrepEdge))
  have hCellRecorded :
      ∀ i : ι, ∀ ω : TwoBiteSample n m p,
        hist i ω →
          ∀ e,
            e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
              e ∈ recorded i := by
    intro i ω hhist e
    exact
      FixedSetPreTerminalReplayUniqueness I (recorded i) (rep i) ω
        (hRepRecorded i)
        (fun x => (hhist.1 x).symm)
        (fun c hc => (hhist.2 c hc).symm)
        e
  have hCover :
      ∀ ω : TwoBiteSample n m p,
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I ↔ ∃ i : ι, hist i ω := by
    intro ω
    constructor
    · intro hω
      let i : ι := ⟨transcript ω, ⟨ω, hω, rfl⟩⟩
      refine ⟨i, hHistFromTranscript i ω ?_⟩
      simpa [i] using (hRepSpec i).2
    · rintro ⟨i, hhist⟩
      have hrepEvent := (hRepSpec i).1
      have hRed :
          TwoBiteRedProjection ω = TwoBiteRedProjection (rep i) := by
        funext x
        simp [TwoBiteRedProjection, TwoBiteEmbedding, hhist.1 x]
      have hBlue :
          TwoBiteBlueProjection ω = TwoBiteBlueProjection (rep i) := by
        funext x
        simp [TwoBiteBlueProjection, TwoBiteEmbedding, hhist.1 x]
      simpa [TwoBiteProjectionSizeEvent, hRed, hBlue] using hrepEvent
  have hEvent :
      ∀ i : ι, ∀ ω : TwoBiteSample n m p,
        hist i ω →
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
            (ℓB := ℓB) ω I := by
    intro i ω hhist
    exact (hCover ω).2 ⟨i, hhist⟩
  have hDisjoint :
      ∀ i j : ι, i ≠ j → ∀ ω : TwoBiteSample n m p,
        ¬ (hist i ω ∧ hist j ω) := by
    intro i j hij ω hboth
    apply hij
    apply Subtype.ext
    calc
      i.1 = transcript (rep i) := (hRepSpec i).2.symm
      _ = transcript (rep j) := by
        apply Prod.ext
        · apply DFunLike.ext
          intro x
          exact ((hboth.1.1 x).symm.trans (hboth.2.1 x))
        · apply Prod.ext
          · apply Finset.ext
            intro e
            constructor
            · intro hei
              have hreci : e ∈ recorded i := (hRepRecorded i e).1 hei
              have hω : e ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
                (hCellRecorded i ω hboth.1 e).2 hreci
              have hrecj : e ∈ recorded j :=
                (hCellRecorded j ω hboth.2 e).1 hω
              exact (hRepRecorded j e).2 hrecj
            · intro hej
              have hrecj : e ∈ recorded j := (hRepRecorded j e).1 hej
              have hω : e ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
                (hCellRecorded j ω hboth.2 e).2 hrecj
              have hreci : e ∈ recorded i :=
                (hCellRecorded i ω hboth.1 e).1 hω
              exact (hRepRecorded i e).2 hreci
          · apply Finset.ext
            intro e
            constructor
            · intro hei
              have hmemi :
                  e ∈ TwoBitePreTerminalRecordedPairs (rep i) ε I ∧
                    TwoBiteEdgeCoordinateValue (rep i) e := by
                simpa [transcript, edgeRecord] using hei
              have hreci : e ∈ recorded i := (hRepRecorded i e).1 hmemi.1
              have hωmem : e ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
                (hCellRecorded i ω hboth.1 e).2 hreci
              have hωedge : TwoBiteEdgeCoordinateValue ω e :=
                (hboth.1.2 e hreci).2 hmemi.2
              have hrecj : e ∈ recorded j :=
                (hCellRecorded j ω hboth.2 e).1 hωmem
              have hptj :
                  e ∈ TwoBitePreTerminalRecordedPairs (rep j) ε I :=
                (hRepRecorded j e).2 hrecj
              have hedgej : TwoBiteEdgeCoordinateValue (rep j) e :=
                (hboth.2.2 e hrecj).1 hωedge
              simp [transcript, edgeRecord, hptj, hedgej]
            · intro hej
              have hmemj :
                  e ∈ TwoBitePreTerminalRecordedPairs (rep j) ε I ∧
                    TwoBiteEdgeCoordinateValue (rep j) e := by
                simpa [transcript, edgeRecord] using hej
              have hrecj : e ∈ recorded j := (hRepRecorded j e).1 hmemj.1
              have hωmem : e ∈ TwoBitePreTerminalRecordedPairs ω ε I :=
                (hCellRecorded j ω hboth.2 e).2 hrecj
              have hωedge : TwoBiteEdgeCoordinateValue ω e :=
                (hboth.2.2 e hrecj).2 hmemj.2
              have hreci : e ∈ recorded i :=
                (hCellRecorded i ω hboth.1 e).1 hωmem
              have hpti :
                  e ∈ TwoBitePreTerminalRecordedPairs (rep i) ε I :=
                (hRepRecorded i e).2 hreci
              have hedgei : TwoBiteEdgeCoordinateValue (rep i) e :=
                (hboth.1.2 e hreci).1 hωedge
              simp [transcript, edgeRecord, hpti, hedgei]
      _ = j.1 := (hRepSpec j).2
  have hRepHist : ∀ i : ι, hist i (rep i) := by
    intro i
    exact hHistFromTranscript i (rep i) rfl
  have hCylinder :
      ∀ i : ι, ∀ ω : TwoBiteSample n m p,
        hist i ω ↔
          (∀ x : Fin n, ω.2.2 x = (rep i).2.2 x) ∧
          (∀ e,
            e ∈ recorded i →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue (rep i) e)) := by
    intro i ω
    rfl
  have hReplayPreservation :
      ∀ i : ι, ∀ ω : TwoBiteSample n m p,
        hist i ω →
          ∀ ω' : TwoBiteSample n m p,
            (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
            (∀ c,
              c ∈ recorded i →
                (TwoBiteEdgeCoordinateValue ω c ↔
                  TwoBiteEdgeCoordinateValue ω' c)) →
              (∀ x,
                TwoBiteStageRevealedVertex ω ε I x ↔
                  TwoBiteStageRevealedVertex ω' ε I x) ∧
              (∀ e,
                TwoBiteProjectionPairTouched ω ε I e ↔
                  TwoBiteProjectionPairTouched ω' ε I e) := by
    intro i ω hhist ω' hEmbedding hEdge
    exact
      FixedSetPreTerminalStageTouchPreservation I (recorded i) ω ω'
        (hCellRecorded i ω hhist) hEmbedding hEdge
  exact
    ⟨ι, inferInstance, hist, recorded, rep, hCover, hDisjoint, hRepHist,
      hCylinder, hCellRecorded, hEvent, hReplayPreservation⟩
