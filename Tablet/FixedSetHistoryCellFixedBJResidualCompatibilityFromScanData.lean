import Tablet.FixedSetHistoryCellRedResidualDeterministicScanOutputs

open Classical

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualCompatibilityFromScanData]

theorem FixedSetHistoryCellFixedBJResidualCompatibilityFromScanData :
    ∀ {Coord BranchLabel RedLabel : Type} [DecidableEq Coord]
      (terminal B : Finset Coord)
      (J : RedLabel)
      (blueColor : Coord → Prop)
      (blueTrace : BranchLabel → Finset Coord)
      (redSupport : BranchLabel → RedLabel → Finset Coord)
      (transcriptLabels :
        Finset (Finset Coord × Finset Coord × Finset Coord))
      (cellRealized :
        Finset Coord →
          RedLabel →
            BranchLabel →
              (Finset Coord × Finset Coord × Finset Coord) →
                Prop)
      (assignmentCompatible :
        Finset Coord →
          Finset Coord →
            RedLabel →
              BranchLabel →
                (Finset Coord × Finset Coord × Finset Coord) →
                  Prop)
      (scanTranscript :
        Finset Coord → Option (Finset Coord × Finset Coord × Finset Coord)),
      (∀ β β' : BranchLabel,
        (∀ e, e ∈ terminal → blueColor e →
          (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
        β = β') →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            redSupport β J ⊆ terminal ∧
            (∀ e, e ∈ redSupport β J → ¬ blueColor e) ∧
            τ.1 ⊆ terminal ∧
            τ.2.1 ⊆ terminal ∧
            Disjoint τ.1 τ.2.1 ∧
            B ∪ redSupport β J ⊆ τ.1 ∧
            (∀ e,
              e ∈ terminal →
                blueColor e →
                  (e ∈ blueTrace β ↔ e ∈ τ.1) ∧
                  (e ∉ blueTrace β ↔ e ∈ τ.2.1)) ∧
            τ.2.2 ⊆ τ.2.1) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              assignmentCompatible A B J β τ →
                τ.1 ⊆ A ∧
                Disjoint (τ.2.1 \ τ.2.2) A ∧
                ∀ e,
                  e ∈ terminal →
                    blueColor e →
                      (e ∈ blueTrace β ↔ e ∈ A)) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              (τ.1 \ (B ∪ redSupport β J)) ⊆ A →
                Disjoint (τ.2.1 \ τ.2.2) A →
                  scanTranscript
                      ((A \ τ.2.2) ∪ (B ∪ redSupport β J)) =
                    some τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              τ.1 ⊆ A →
                Disjoint τ.2.1 A →
              (∀ e,
                e ∈ terminal →
                  blueColor e →
                    (e ∈ blueTrace β ↔ e ∈ A)) →
                scanTranscript A = some τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              τ.1 ⊆ A →
                Disjoint τ.2.1 A →
              (∀ e,
                e ∈ terminal →
                  blueColor e →
                    (e ∈ blueTrace β ↔ e ∈ A)) →
                scanTranscript A = some τ →
                  assignmentCompatible A B J β τ) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  (τ.1 \ (B ∪ redSupport β J)) ⊆ A →
                    Disjoint (τ.2.1 \ τ.2.2) A →
                      (τ'.1 \ (B ∪ redSupport β' J)) ⊆ A →
                        Disjoint (τ'.2.1 \ τ'.2.2) A →
                          assignmentCompatible
                            ((A \ τ.2.2) ∪ (B ∪ redSupport β J))
                            B J β τ →
                          assignmentCompatible
                            ((A \ τ'.2.2) ∪ (B ∪ redSupport β' J))
                            B J β' τ' →
                            β = β' ∧ τ = τ') →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              (τ.1 \ (B ∪ redSupport β J)) ⊆ A →
                Disjoint (τ.2.1 \ τ.2.2) A →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ (B ∪ redSupport β J))
                    B J β τ) ∧
      ∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ (B ∪ redSupport β J))
                    B J β τ →
                  assignmentCompatible
                    ((A \ τ'.2.2) ∪ (B ∪ redSupport β' J))
                    B J β' τ' →
                    β = β' ∧ τ = τ' := by
-- BODY
  classical
  intro Coord BranchLabel RedLabel _ terminal B J blueColor blueTrace
    redSupport transcriptLabels cellRealized assignmentCompatible
    scanTranscript hbranchFunctional hgeometry hcompatForward
    hresidualScanStable hscanRecognizesFull hcompatConverse
    hfirstMismatchUnique
  have hdeterministic :=
    FixedSetHistoryCellRedResidualDeterministicScanOutputs
      (terminal := terminal) (B := B) (J := J)
      (blueColor := blueColor) (blueTrace := blueTrace)
      (redSupport := redSupport) (transcriptLabels := transcriptLabels)
      (cellRealized := cellRealized)
      (assignmentCompatible := assignmentCompatible)
      (scanTranscript := scanTranscript)
      hbranchFunctional hgeometry hcompatForward hresidualScanStable
      hscanRecognizesFull hfirstMismatchUnique
  constructor
  · intro A β τ hA hτ hreal hpresentResidual habsentResidual
    let reconstructed : Finset Coord :=
      (A \ τ.2.2) ∪ (B ∪ redSupport β J)
    rcases hgeometry β τ hτ hreal with
      ⟨_hRedSupportTerminal, _hRedSupportNotBlue, hPresentTerminal,
        _hAbsentTerminal, hPresentAbsent, hFixedPresent, hBlueTranscript,
        hSelectedAbsent⟩
    have hReconstructedTerminal : reconstructed ⊆ terminal := by
      intro e he
      rcases Finset.mem_union.mp he with heA | heFixed
      · exact hA (Finset.mem_sdiff.mp heA).1
      · exact hPresentTerminal (hFixedPresent heFixed)
    have hPresentReconstructed : τ.1 ⊆ reconstructed := by
      intro e hePresent
      by_cases heFixed : e ∈ B ∪ redSupport β J
      · exact Finset.mem_union.mpr (Or.inr heFixed)
      · have heA : e ∈ A :=
          hpresentResidual (Finset.mem_sdiff.mpr ⟨hePresent, heFixed⟩)
        have heNotSelected : e ∉ τ.2.2 := by
          intro heSelected
          exact
            (Finset.disjoint_left.mp hPresentAbsent hePresent)
              (hSelectedAbsent heSelected)
        exact
          Finset.mem_union.mpr
            (Or.inl (Finset.mem_sdiff.mpr ⟨heA, heNotSelected⟩))
    have hAbsentReconstructed : Disjoint τ.2.1 reconstructed := by
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
            blueColor e →
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
          have heAbsent : e ∈ τ.2.1 :=
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
  · exact hdeterministic.2
