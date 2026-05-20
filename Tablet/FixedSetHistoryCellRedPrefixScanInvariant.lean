import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedPrefixScanInvariant]

theorem FixedSetHistoryCellRedPrefixScanInvariant :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord]
      (terminal : Finset Coord)
      (prefixBefore : Coord → Finset Coord)
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset Coord → Coord → Prop)
      (blueCoord : Coord → Prop)
      (blueTrace : BranchLabel → Finset Coord)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport openCandidate : BranchLabel → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible :
        Finset Coord → BranchLabel → Transcript → Prop)
      (selectedPresentSibling :
        Finset Coord → BranchLabel → Transcript → Coord → Prop)
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
          fixedSupport β ⊆ present τ ∧
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
                  e ∈ fixedSupport β) →
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized β τ →
            e ∈ selected τ →
              selectedPresentSibling A β τ e →
                ∀ β' τ',
                  cellRealized β' τ' →
                    ¬ assignmentCompatible A β' τ') ∧
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              β = branchOfAssignment A ∧
                  scanTranscript A = some τ) := by
-- BODY
  intro Coord BranchLabel Transcript _ terminal prefixBefore stagedOpen touched
    sameColorClosed preTerminalRecorded blueCoord blueTrace present absent
    selected fixedSupport openCandidate cellRealized assignmentCompatible
    selectedPresentSibling branchOfAssignment scanTranscript _hprefixBefore
    _hprefixSafety hblueFunctional hbranchOfAssignment hscanTranscript
    hsiblingSelected hcellGeometry hcompatibleBlue hsiblingData
    hfixedSupportExhaustion
  have hprune :
      ∀ A β τ e,
        A ⊆ terminal →
          cellRealized β τ →
            e ∈ selected τ →
              selectedPresentSibling A β τ e →
                ∀ β' τ',
                  cellRealized β' τ' →
                    ¬ assignmentCompatible A β' τ' := by
    intro A β τ e hA hreal heSelected hsibling β' τ' hreal' hcompat'
    rcases hcellGeometry β τ hreal with
      ⟨hfixed_subset, hpresent_absent, _hselected_absent, hselected_open⟩
    rcases hsiblingData A β τ e hA hreal heSelected hsibling with
      ⟨heA, hblueA⟩
    have hblueA' := hcompatibleBlue A β' τ' hA hreal' hcompat'
    have hβ' : β' = β := by
      apply hblueFunctional
      intro c hc hblue
      exact (hblueA' c hc hblue).trans ((hblueA c hc hblue).symm)
    have hopen' : e ∈ openCandidate β' := by
      simpa [hβ'] using hselected_open heSelected
    have hfixed' :
        e ∈ fixedSupport β' :=
      hfixedSupportExhaustion A β' τ' e hA hreal' hcompat' hopen' heA
    have hfixed : e ∈ fixedSupport β := by
      simpa [hβ'] using hfixed'
    have hpresent : e ∈ present τ := hfixed_subset hfixed
    have habsent : e ∈ absent τ := _hselected_absent heSelected
    exact (Finset.disjoint_left.mp hpresent_absent hpresent) habsent
  constructor
  · exact hprune
  · intro A β τ hA hreal hcompat
    have hnoSibling : ∀ e, ¬ selectedPresentSibling A β τ e := by
      intro e hsibling
      exact
        (hprune A β τ e hA hreal
          (hsiblingSelected A β τ e hsibling) hsibling β τ hreal) hcompat
    have hblueA := hcompatibleBlue A β τ hA hreal hcompat
    exact
      ⟨hbranchOfAssignment A β τ hA hreal hcompat hblueA,
        hscanTranscript A β τ hA hreal hcompat hnoSibling⟩
