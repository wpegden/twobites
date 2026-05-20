import Tablet.FixedSetHistoryCellRedPrefixScanInvariant

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualOverlapConsistency]

theorem FixedSetHistoryCellFixedBJResidualOverlapConsistency :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport : BranchLabel → Transcript → Finset Coord)
      (prefixFixedSupport openCandidate : BranchLabel → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible :
        Finset Coord → BranchLabel → Transcript → Prop)
      (selectedPresentSibling :
        Finset Coord → BranchLabel → Transcript → Coord → Prop)
      (prefixBefore : Coord → Finset Coord)
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset Coord → Coord → Prop)
      (blueCoord : Coord → Prop)
      (blueTrace : BranchLabel → Finset Coord)
      (branchOfAssignment : Finset Coord → BranchLabel)
      (scanTranscript : Finset Coord → Option Transcript),
      (∀ e, prefixBefore e ⊆ terminal) →
      (∀ A A' e,
        A ⊆ terminal →
          A' ⊆ terminal →
            (∀ c, c ∈ prefixBefore e → (c ∈ A ↔ c ∈ A')) →
              (stagedOpen A e ↔ stagedOpen A' e) ∧
              (touched A e ↔ touched A' e) ∧
              (sameColorClosed A e ↔ sameColorClosed A' e) ∧
              (preTerminalRecorded A e ↔ preTerminalRecorded A' e)) →
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            blueCoord e →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              (∀ e,
                e ∈ terminal →
                  blueCoord e →
                    (e ∈ blueTrace β ↔ e ∈ A)) →
                β = branchOfAssignment A) →
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              (∀ e, ¬ selectedPresentSibling A β τ e) →
                scanTranscript A = some τ) →
      (∀ A β τ e,
        selectedPresentSibling A β τ e →
          e ∈ selected τ) →
      (∀ β τ,
        cellRealized β τ →
          prefixFixedSupport β ⊆ present τ ∧
          Disjoint (present τ) (absent τ) ∧
          selected τ ⊆ absent τ ∧
          selected τ ⊆ openCandidate β) →
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              ∀ e,
                e ∈ terminal →
                  blueCoord e →
                    (e ∈ blueTrace β ↔ e ∈ A)) →
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized β τ →
            e ∈ selected τ →
              selectedPresentSibling A β τ e →
                e ∈ A ∧
                ∀ c,
                  c ∈ terminal →
                    blueCoord c →
                      (c ∈ blueTrace β ↔ c ∈ A)) →
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              e ∈ openCandidate β →
                e ∈ A →
                  e ∈ prefixFixedSupport β) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            fixedSupport β τ ⊆ present τ ∧
            present τ ⊆ terminal ∧
            absent τ ⊆ terminal ∧
            Disjoint (present τ) (absent τ) ∧
            selected τ ⊆ absent τ) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  (present τ \ fixedSupport β τ) ⊆ A →
                    Disjoint (absent τ \ selected τ) A →
                      (present τ' \ fixedSupport β' τ') ⊆ A →
                        Disjoint (absent τ' \ selected τ') A →
                          assignmentCompatible
                            ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                          assignmentCompatible
                            ((A \ selected τ') ∪ fixedSupport β' τ') β' τ' →
                          (β ≠ β' ∨ τ ≠ τ') →
                            (∃ e,
                              e ∈ selected τ ∧
                                selectedPresentSibling
                                  ((A \ selected τ) ∪ fixedSupport β τ)
                                  β τ e) ∨
                            (∃ e,
                              e ∈ selected τ' ∧
                                selectedPresentSibling
                                  ((A \ selected τ') ∪ fixedSupport β' τ')
                                  β' τ' e)) →
      ∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  (present τ \ fixedSupport β τ) ⊆ A →
                    Disjoint (absent τ \ selected τ) A →
                      (present τ' \ fixedSupport β' τ') ⊆ A →
                        Disjoint (absent τ' \ selected τ') A →
                          assignmentCompatible
                            ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                          assignmentCompatible
                            ((A \ selected τ') ∪ fixedSupport β' τ') β' τ' →
                            β = β' ∧ τ = τ' := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ terminal transcriptLabels present
    absent selected fixedSupport prefixFixedSupport openCandidate
    cellRealized assignmentCompatible selectedPresentSibling prefixBefore
    stagedOpen touched sameColorClosed preTerminalRecorded blueCoord
    blueTrace branchOfAssignment scanTranscript hprefixBefore hprefixSafety
    hblueFunctional hbranchOfAssignment hscanTranscript hsiblingSelected
    hprefixCellGeometry hcompatibleBlue hsiblingData
    hfixedSupportExhaustion hrealizedGeometry hfirstMismatch A β β' τ τ'
    hA hτ hτ' hreal hreal' hpresent_res habsent_res hpresent_res'
    habsent_res' hcompat hcompat'
  have hprefix :=
    FixedSetHistoryCellRedPrefixScanInvariant
      (terminal := terminal) (prefixBefore := prefixBefore)
      (stagedOpen := stagedOpen) (touched := touched)
      (sameColorClosed := sameColorClosed)
      (preTerminalRecorded := preTerminalRecorded)
      (blueCoord := blueCoord) (blueTrace := blueTrace)
      (present := present) (absent := absent) (selected := selected)
      (fixedSupport := prefixFixedSupport) (openCandidate := openCandidate)
      (cellRealized := cellRealized)
      (assignmentCompatible := assignmentCompatible)
      (selectedPresentSibling := selectedPresentSibling)
      (branchOfAssignment := branchOfAssignment)
      (scanTranscript := scanTranscript)
      hprefixBefore hprefixSafety hblueFunctional hbranchOfAssignment
      hscanTranscript hsiblingSelected hprefixCellGeometry
      hcompatibleBlue hsiblingData hfixedSupportExhaustion
  rcases hprefix with ⟨hprune, _hscanOutputs⟩
  by_contra hnot
  have hmismatch : β ≠ β' ∨ τ ≠ τ' := by
    by_cases hβ : β = β'
    · right
      intro hτeq
      exact hnot ⟨hβ, hτeq⟩
    · exact Or.inl hβ
  have hrec_subset :
      ((A \ selected τ) ∪ fixedSupport β τ) ⊆ terminal := by
    intro c hc
    rcases Finset.mem_union.mp hc with hcA | hcfixed
    · exact hA (Finset.mem_sdiff.mp hcA).1
    · exact (hrealizedGeometry β τ hτ hreal).2.1
        ((hrealizedGeometry β τ hτ hreal).1 hcfixed)
  have hrec_subset' :
      ((A \ selected τ') ∪ fixedSupport β' τ') ⊆ terminal := by
    intro c hc
    rcases Finset.mem_union.mp hc with hcA | hcfixed
    · exact hA (Finset.mem_sdiff.mp hcA).1
    · exact (hrealizedGeometry β' τ' hτ' hreal').2.1
        ((hrealizedGeometry β' τ' hτ' hreal').1 hcfixed)
  have hsibling :=
    hfirstMismatch A β β' τ τ' hA hτ hτ' hreal hreal'
      hpresent_res habsent_res hpresent_res' habsent_res' hcompat
      hcompat' hmismatch
  rcases hsibling with hsibling | hsibling'
  · rcases hsibling with ⟨e, heSelected, hsib⟩
    exact
      (hprune ((A \ selected τ) ∪ fixedSupport β τ) β τ e
        hrec_subset hreal heSelected hsib β τ hreal) hcompat
  · rcases hsibling' with ⟨e, heSelected, hsib⟩
    exact
      (hprune ((A \ selected τ') ∪ fixedSupport β' τ') β' τ' e
        hrec_subset' hreal' heSelected hsib β' τ' hreal') hcompat'
