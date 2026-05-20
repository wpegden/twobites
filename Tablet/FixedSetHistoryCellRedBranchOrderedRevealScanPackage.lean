import Tablet.FixedSetHistoryCellFixedBJResidualOverlapConsistency
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRedBranchScanInterfaceConstruction
import Tablet.FixedSetHistoryCellRedPrefixScanInvariant
import Tablet.FixedSetHistoryCellRedResidualDeterministicScanOutputs
import Tablet.FixedSetHistoryCellTerminalAssignmentExtension

open Classical

-- [TABLET NODE: FixedSetHistoryCellRedBranchOrderedRevealScanPackage]

theorem FixedSetHistoryCellRedBranchOrderedRevealScanPackage :
    ∀ {Coord BranchLabel RedLabel Transcript : Type} [DecidableEq Coord]
      (terminal B : Finset Coord)
      (J : RedLabel)
      (order : List Coord)
      (blueCoord : Coord → Prop)
      (blueTrace : BranchLabel → Finset Coord)
      (redSupport : BranchLabel → RedLabel → Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (cellRealized :
        Finset Coord → RedLabel → BranchLabel → Transcript → Prop)
      (assignmentCompatible :
        Finset Coord → Finset Coord → RedLabel → BranchLabel →
          Transcript → Prop)
      (scanTranscript : Finset Coord → Option Transcript)
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset Coord → Coord → Prop)
      (witness : BranchLabel → Transcript → Finset Coord)
      (dependencySet : BranchLabel → Transcript → Coord → Finset Coord)
      (prefixBefore : Coord → Finset Coord)
      (prefixFixedSupport openCandidate : BranchLabel → Finset Coord)
      (selectedPresentSibling :
        Finset Coord → BranchLabel → Transcript → Coord → Prop),
      order.Nodup →
      order.toFinset = terminal →
      (∀ β β' : BranchLabel,
        (∀ e, e ∈ terminal → blueCoord e →
          (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
        β = β') →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            redSupport β J ⊆ terminal ∧
            (∀ e, e ∈ redSupport β J → ¬ blueCoord e) ∧
            present τ ⊆ terminal ∧
            absent τ ⊆ terminal ∧
            Disjoint (present τ) (absent τ) ∧
            B ∪ redSupport β J ⊆ present τ ∧
            (∀ e,
              e ∈ terminal →
                blueCoord e →
                  (e ∈ blueTrace β ↔ e ∈ present τ) ∧
                  (e ∉ blueTrace β ↔ e ∈ absent τ)) ∧
            selected τ ⊆ absent τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              assignmentCompatible A B J β τ →
                present τ ⊆ A ∧
                Disjoint (absent τ \ selected τ) A ∧
                ∀ e,
                  e ∈ terminal →
                    blueCoord e →
                      (e ∈ blueTrace β ↔ e ∈ A)) →
      (∀ e, prefixBefore e ⊆ terminal) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            witness β τ ⊆ terminal) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e,
              e ∈ present τ → e ∈ witness β τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e,
              e ∈ absent τ → e ∉ witness β τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e,
              e ∈ terminal →
                ∀ c,
                  c ∈ dependencySet β τ e →
                    c ∈ B ∪ redSupport β J ∨
                      c ∈ present τ \
                        (B ∪ redSupport β J) ∨
                      c ∈ selected τ ∨
                        c ∈ absent τ \ selected τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ (pre suffix : List Coord) (e : Coord),
              order = pre ++ e :: suffix →
                dependencySet β τ e ⊆ pre.toFinset) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ A,
              A ⊆ terminal →
                ∀ e,
                  e ∈ terminal →
                    (∀ c,
                      c ∈ dependencySet β τ e →
                        (c ∈ witness β τ ↔ c ∈ A)) →
                    (stagedOpen (witness β τ) e ↔ stagedOpen A e) ∧
                    (touched (witness β τ) e ↔ touched A e) ∧
                    (sameColorClosed (witness β τ) e ↔
                      sameColorClosed A e) ∧
                    (preTerminalRecorded (witness β τ) e ↔
                      preTerminalRecorded A e)) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              (present τ \ (B ∪ redSupport β J)) ⊆ A →
                Disjoint (absent τ \ selected τ) A →
                  scanTranscript
                      ((A \ selected τ) ∪ (B ∪ redSupport β J)) =
                    some τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              present τ ⊆ A →
                Disjoint (absent τ) A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ blueTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              present τ ⊆ A →
                Disjoint (absent τ) A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ blueTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ →
                      assignmentCompatible A B J β τ) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  assignmentCompatible
                    ((A \ selected τ) ∪
                      (B ∪ redSupport β J)) B J β τ →
                  assignmentCompatible
                    ((A \ selected τ') ∪
                      (B ∪ redSupport β' J)) B J β' τ' →
                    β = β' ∧ τ = τ') →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  (present τ \ (B ∪ redSupport β J)) ⊆ A →
                    Disjoint (absent τ \ selected τ) A →
                      (present τ' \ (B ∪ redSupport β' J)) ⊆ A →
                        Disjoint (absent τ' \ selected τ') A →
                          assignmentCompatible
                            ((A \ selected τ) ∪
                              (B ∪ redSupport β J)) B J β τ →
                          assignmentCompatible
                            ((A \ selected τ') ∪
                              (B ∪ redSupport β' J)) B J β' τ' →
                          (β ≠ β' ∨ τ ≠ τ') →
                            (∃ e,
                              e ∈ selected τ ∧
                                selectedPresentSibling
                                  ((A \ selected τ) ∪
                                    (B ∪ redSupport β J))
                                  β τ e) ∨
                            (∃ e,
                              e ∈ selected τ' ∧
                                selectedPresentSibling
                                  ((A \ selected τ') ∪
                                    (B ∪ redSupport β' J))
                                  β' τ' e)) →
        ((∀ A β τ,
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                (present τ \ (B ∪ redSupport β J)) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    assignmentCompatible
                      ((A \ selected τ) ∪ (B ∪ redSupport β J))
                      B J β τ) ∧
        (∀ A β β' τ τ',
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              τ' ∈ transcriptLabels →
                cellRealized B J β τ →
                  cellRealized B J β' τ' →
                    assignmentCompatible
                      ((A \ selected τ) ∪ (B ∪ redSupport β J))
                      B J β τ →
                    assignmentCompatible
                      ((A \ selected τ') ∪ (B ∪ redSupport β' J))
                      B J β' τ' →
                      β = β' ∧ τ = τ')) ∧
        (∀ e, prefixBefore e ⊆ terminal) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              witness β τ ⊆ terminal) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              ∀ e,
                e ∈ present τ → e ∈ witness β τ) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              ∀ e,
                e ∈ absent τ → e ∉ witness β τ) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              ∀ e,
                e ∈ terminal →
                  ∀ c,
                    c ∈ dependencySet β τ e →
                      c ∈ B ∪ redSupport β J ∨
                        c ∈ present τ \
                          (B ∪ redSupport β J) ∨
                        c ∈ selected τ ∨
                          c ∈ absent τ \ selected τ) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              ∀ (pre suffix : List Coord) (e : Coord),
                order = pre ++ e :: suffix →
                  dependencySet β τ e ⊆ pre.toFinset) ∧
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              ∀ A,
                A ⊆ terminal →
                  ∀ e,
                    e ∈ terminal →
                      (∀ c,
                        c ∈ dependencySet β τ e →
                          (c ∈ witness β τ ↔ c ∈ A)) →
                      (stagedOpen (witness β τ) e ↔ stagedOpen A e) ∧
                      (touched (witness β τ) e ↔ touched A e) ∧
                      (sameColorClosed (witness β τ) e ↔
                        sameColorClosed A e) ∧
                      (preTerminalRecorded (witness β τ) e ↔
                        preTerminalRecorded A e)) ∧
        (∀ A β τ,
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                (present τ \ (B ∪ redSupport β J)) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    scanTranscript
                        ((A \ selected τ) ∪
                          (B ∪ redSupport β J)) =
                      some τ) ∧
        (∀ A β τ,
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                present τ ⊆ A →
                  Disjoint (absent τ) A →
                    (∀ e,
                      e ∈ terminal →
                        blueCoord e →
                          (e ∈ blueTrace β ↔ e ∈ A)) →
                      scanTranscript A = some τ) ∧
        (∀ A β β' τ τ',
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              τ' ∈ transcriptLabels →
                cellRealized B J β τ →
                  cellRealized B J β' τ' →
                    (present τ \ (B ∪ redSupport β J)) ⊆ A →
                      Disjoint (absent τ \ selected τ) A →
                        (present τ' \ (B ∪ redSupport β' J)) ⊆ A →
                          Disjoint (absent τ' \ selected τ') A →
                            assignmentCompatible
                              ((A \ selected τ) ∪
                                (B ∪ redSupport β J)) B J β τ →
                            assignmentCompatible
                              ((A \ selected τ') ∪
                                (B ∪ redSupport β' J)) B J β' τ' →
                            (β ≠ β' ∨ τ ≠ τ') →
                              (∃ e,
                                e ∈ selected τ ∧
                                  selectedPresentSibling
                                    ((A \ selected τ) ∪
                                      (B ∪ redSupport β J))
                                    β τ e) ∨
                              (∃ e,
                                e ∈ selected τ' ∧
                                  selectedPresentSibling
                                    ((A \ selected τ') ∪
                                      (B ∪ redSupport β' J))
                                    β' τ' e)) := by
-- BODY
  classical
  intro Coord BranchLabel RedLabel Transcript _ terminal B J order blueCoord
    blueTrace redSupport transcriptLabels present absent selected
    cellRealized assignmentCompatible scanTranscript stagedOpen touched
    sameColorClosed preTerminalRecorded witness dependencySet prefixBefore
    prefixFixedSupport openCandidate selectedPresentSibling _horderNodup
    _horderTerminal _hbranchFunctional hgeometry _hcompatForward
    hprefixBefore hwitnessTerminal hwitnessPresent hwitnessAbsent
    hreadClassified hdependenciesPast hexactReadStability
    hresidualScanStable hfullScanRecognizes hcompatConverse
    hresidualOwnerUnique hfirstMismatchSibling
  refine
    ⟨⟨?residualCompat, hresidualOwnerUnique⟩, hprefixBefore,
      hwitnessTerminal, hwitnessPresent, hwitnessAbsent, hreadClassified,
      hdependenciesPast, hexactReadStability, hresidualScanStable,
      hfullScanRecognizes, hfirstMismatchSibling⟩
  intro A β τ hA hτ hreal hpresentResidual habsentResidual
  let reconstructed : Finset Coord :=
    (A \ selected τ) ∪ (B ∪ redSupport β J)
  rcases hgeometry β τ hτ hreal with
    ⟨_hRedSupportTerminal, _hRedSupportNotBlue, hPresentTerminal,
      _hAbsentTerminal, hPresentAbsent, hFixedPresent, hBlueTranscript,
      hSelectedAbsent⟩
  have hReconstructedTerminal : reconstructed ⊆ terminal := by
    intro e he
    rcases Finset.mem_union.mp he with heA | heFixed
    · exact hA (Finset.mem_sdiff.mp heA).1
    · exact hPresentTerminal (hFixedPresent heFixed)
  have hPresentReconstructed : present τ ⊆ reconstructed := by
    intro e hePresent
    by_cases heFixed : e ∈ B ∪ redSupport β J
    · exact Finset.mem_union.mpr (Or.inr heFixed)
    · have heA : e ∈ A :=
        hpresentResidual (Finset.mem_sdiff.mpr ⟨hePresent, heFixed⟩)
      have heNotSelected : e ∉ selected τ := by
        intro heSelected
        exact
          (Finset.disjoint_left.mp hPresentAbsent hePresent)
            (hSelectedAbsent heSelected)
      exact
        Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨heA, heNotSelected⟩))
  have hAbsentReconstructed : Disjoint (absent τ) reconstructed := by
    rw [Finset.disjoint_left]
    intro e heAbsent heReconstructed
    rcases Finset.mem_union.mp heReconstructed with heA | heFixed
    · rcases Finset.mem_sdiff.mp heA with ⟨heA_mem, heNotSelected⟩
      exact
        (Finset.disjoint_left.mp habsentResidual
          (Finset.mem_sdiff.mpr ⟨heAbsent, heNotSelected⟩)) heA_mem
    · exact
        (Finset.disjoint_left.mp hPresentAbsent (hFixedPresent heFixed))
          heAbsent
  have hBlueReconstructed :
      ∀ e,
        e ∈ terminal →
          blueCoord e →
            (e ∈ blueTrace β ↔ e ∈ reconstructed) := by
    intro e heTerminal heBlue
    constructor
    · intro heTrace
      exact hPresentReconstructed
        ((hBlueTranscript e heTerminal heBlue).1.mp heTrace)
    · intro heReconstructed
      rcases Finset.mem_union.mp heReconstructed with heA | heFixed
      · rcases Finset.mem_sdiff.mp heA with ⟨heA_mem, heNotSelected⟩
        by_contra heNotTrace
        have heAbsent : e ∈ absent τ :=
          (hBlueTranscript e heTerminal heBlue).2.mp heNotTrace
        exact
          (Finset.disjoint_left.mp habsentResidual
            (Finset.mem_sdiff.mpr ⟨heAbsent, heNotSelected⟩)) heA_mem
      · exact
          (hBlueTranscript e heTerminal heBlue).1.mpr
            (hFixedPresent heFixed)
  have hScan :
      scanTranscript reconstructed = some τ := by
    exact
      hresidualScanStable A β τ hA hτ hreal hpresentResidual
        habsentResidual
  exact
    hcompatConverse reconstructed β τ hReconstructedTerminal hτ hreal
      hPresentReconstructed hAbsentReconstructed hBlueReconstructed hScan
