import Tablet.FixedSetHistoryCellFixedBJResidualOverlapConsistency
import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability

open Classical

-- [TABLET NODE: FixedSetHistoryCellRedResidualDeterministicScanOutputs]

theorem FixedSetHistoryCellRedResidualDeterministicScanOutputs :
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
        Finset Coord →
          Option (Finset Coord × Finset Coord × Finset Coord)),
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
                    ∀ β' τ',
                      τ' ∈ transcriptLabels →
                        cellRealized B J β' τ' →
                          τ'.1 ⊆
                              ((A \ τ.2.2) ∪
                                (B ∪ redSupport β J)) →
                            Disjoint τ'.2.1
                              ((A \ τ.2.2) ∪
                                (B ∪ redSupport β J)) →
                        (∀ e,
                          e ∈ terminal →
                            blueColor e →
                              (e ∈ blueTrace β' ↔
                                e ∈ ((A \ τ.2.2) ∪
                                  (B ∪ redSupport β J)))) →
                          τ' = τ) ∧
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
    scanTranscript _hbranchFunctional hgeometry hcompatForward
    hresidualScanStable hscanRecognizesFull hfirstMismatchUnique
  constructor
  · intro A β τ hA hτ hreal hpresent_res habsent_res β' τ' hτ' hreal'
      hpresent' habsent' hblue'
    let reconstructed : Finset Coord :=
      (A \ τ.2.2) ∪ (B ∪ redSupport β J)
    rcases hgeometry β τ hτ hreal with
      ⟨_hRsub, _hRnotBlue, hPsub, _hAsub, _hDisj, hFixed,
        _hBlue, _hZsub⟩
    have hrec_terminal : reconstructed ⊆ terminal := by
      intro e he
      rcases Finset.mem_union.mp he with heA | hfixed
      · exact hA (Finset.mem_sdiff.mp heA).1
      · exact hPsub (hFixed hfixed)
    have hscanτ :
        scanTranscript reconstructed = some τ := by
      exact hresidualScanStable A β τ hA hτ hreal hpresent_res
        habsent_res
    have hscanτ' :
        scanTranscript reconstructed = some τ' := by
      exact hscanRecognizesFull reconstructed β' τ' hrec_terminal hτ' hreal'
        hpresent' habsent' hblue'
    exact Option.some.inj (hscanτ'.symm.trans hscanτ)
  · intro A β β' τ τ' hA hτ hτ' hreal hreal' hcompat hcompat'
    let reconstructed :
        Finset Coord :=
      (A \ τ.2.2) ∪ (B ∪ redSupport β J)
    let reconstructed' :
        Finset Coord :=
      (A \ τ'.2.2) ∪ (B ∪ redSupport β' J)
    rcases hgeometry β τ hτ hreal with
      ⟨_hRsub, _hRnotBlue, hPsub, _hAsub, _hDisj, hFixed,
        _hBlue, _hZsub⟩
    rcases hgeometry β' τ' hτ' hreal' with
      ⟨_hRsub', _hRnotBlue', hPsub', _hAsub', _hDisj', hFixed',
        _hBlue', _hZsub'⟩
    have hrec_terminal : reconstructed ⊆ terminal := by
      intro e he
      rcases Finset.mem_union.mp he with heA | hfixed
      · exact hA (Finset.mem_sdiff.mp heA).1
      · exact hPsub (hFixed hfixed)
    have hrec'_terminal : reconstructed' ⊆ terminal := by
      intro e he
      rcases Finset.mem_union.mp he with heA | hfixed
      · exact hA (Finset.mem_sdiff.mp heA).1
      · exact hPsub' (hFixed' hfixed)
    have hforward :=
      hcompatForward reconstructed β τ hrec_terminal hτ hreal hcompat
    have hforward' :=
      hcompatForward reconstructed' β' τ' hrec'_terminal hτ' hreal'
        hcompat'
    have hpresent_res : (τ.1 \ (B ∪ redSupport β J)) ⊆ A := by
      intro e he
      rcases Finset.mem_sdiff.mp he with ⟨hePresent, heNotFixed⟩
      have herec : e ∈ reconstructed := hforward.1 hePresent
      rcases Finset.mem_union.mp herec with heA | hfixed
      · exact (Finset.mem_sdiff.mp heA).1
      · exact False.elim (heNotFixed hfixed)
    have hpresent_res' : (τ'.1 \ (B ∪ redSupport β' J)) ⊆ A := by
      intro e he
      rcases Finset.mem_sdiff.mp he with ⟨hePresent, heNotFixed⟩
      have herec : e ∈ reconstructed' := hforward'.1 hePresent
      rcases Finset.mem_union.mp herec with heA | hfixed
      · exact (Finset.mem_sdiff.mp heA).1
      · exact False.elim (heNotFixed hfixed)
    have habsent_res : Disjoint (τ.2.1 \ τ.2.2) A := by
      rw [Finset.disjoint_left]
      intro e heAbsent heA
      have heRec : e ∈ reconstructed := by
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr
            ⟨heA, (Finset.mem_sdiff.mp heAbsent).2⟩))
      exact (Finset.disjoint_left.mp hforward.2.1 heAbsent) heRec
    have habsent_res' : Disjoint (τ'.2.1 \ τ'.2.2) A := by
      rw [Finset.disjoint_left]
      intro e heAbsent heA
      have heRec : e ∈ reconstructed' := by
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr
            ⟨heA, (Finset.mem_sdiff.mp heAbsent).2⟩))
      exact (Finset.disjoint_left.mp hforward'.2.1 heAbsent) heRec
    exact
      hfirstMismatchUnique A β β' τ τ' hA hτ hτ' hreal hreal'
        hpresent_res habsent_res hpresent_res' habsent_res' hcompat hcompat'
