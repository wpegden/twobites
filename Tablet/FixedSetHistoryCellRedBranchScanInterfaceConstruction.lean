import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellTerminalAssignmentExtension
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStagedOpenPairs

open Classical

-- [TABLET NODE: FixedSetHistoryCellRedBranchScanInterfaceConstruction]

theorem FixedSetHistoryCellRedBranchScanInterfaceConstruction :
    ∀ {n m : ℕ} {p ε : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel RedLabel : Type}
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (J : RedLabel)
      (blueTrace :
        BranchLabel → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      (cellRealized :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          RedLabel →
            BranchLabel →
              (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
              Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            RedLabel →
              BranchLabel →
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                Prop)
      (scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      (witness :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (dependencySet :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Sum (Fin m × Fin m) (Fin m × Fin m) →
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
      (prefixBefore :
        Sum (Fin m × Fin m) (Fin m × Fin m) →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (prefixFixedSupport openCandidate :
        BranchLabel → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (selectedPresentSibling :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
              Sum (Fin m × Fin m) (Fin m × Fin m) → Prop),
      order.Nodup →
      order.toFinset = terminal →
      (∀ e,
        e ∈ recorded →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ e,
        e ∈ terminal →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ e,
        e ∈ terminal →
          e ∉ recorded) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre suffix :
              List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ List.toFinset pre →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                  (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                    e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                  (TwoBiteProjectionPairTouched ω ε I e ↔
                    TwoBiteProjectionPairTouched ω' ε I e) ∧
                  (TwoBiteProjectionPairSameColorClosed ω I e ↔
                    TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                  (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) →
      (∀ β τ,
        cellRealized B J β τ →
          τ ∈ transcriptLabels) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            redSupport β J ⊆ terminal ∧
            (∀ e,
              e ∈ redSupport β J →
                ¬
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True)) ∧
            τ.1 ⊆ terminal ∧
            τ.2.1 ⊆ terminal ∧
            Disjoint τ.1 τ.2.1 ∧
            B ∪ redSupport β J ⊆ τ.1 ∧
            (∀ e,
              e ∈ terminal →
                (match e with
                | Sum.inl _ => False
                | Sum.inr _ => True) →
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
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            witness β τ ⊆ terminal) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e, e ∈ τ.1 → e ∈ witness β τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e, e ∈ τ.2.1 → e ∉ witness β τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ e,
              e ∈ terminal →
                ∀ c,
                  c ∈ dependencySet β τ e →
                    c ∈ B ∪ redSupport β J ∨
                      c ∈ τ.1 \ (B ∪ redSupport β J) ∨
                        c ∈ τ.2.2 ∨
                          c ∈ τ.2.1 \ τ.2.2) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ (pre suffix :
                List (Sum (Fin m × Fin m) (Fin m × Fin m)))
              (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
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
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized B J β τ →
            ∀ A,
              A ⊆ terminal →
              (∀ e,
                e ∈ terminal →
                  (stagedOpen (witness β τ) e ↔ stagedOpen A e) ∧
                  (touched (witness β τ) e ↔ touched A e) ∧
                  (sameColorClosed (witness β τ) e ↔
                    sameColorClosed A e) ∧
                  (preTerminalRecorded (witness β τ) e ↔
                    preTerminalRecorded A e)) →
                scanTranscript A = some τ) →
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
            (match e with
            | Sum.inl _ => False
            | Sum.inr _ => True) →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
      (∀ A β τ e,
        selectedPresentSibling A β τ e →
          e ∈ τ.2.2) →
      (∀ β τ,
        cellRealized B J β τ →
          prefixFixedSupport β ⊆ τ.1 ∧
          Disjoint τ.1 τ.2.1 ∧
          τ.2.2 ⊆ τ.2.1 ∧
          τ.2.2 ⊆ openCandidate β) →
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized B J β τ →
            e ∈ τ.2.2 →
              selectedPresentSibling A β τ e →
                e ∈ A ∧
                ∀ c,
                  c ∈ terminal →
                    (match c with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (c ∈ blueTrace β ↔ c ∈ A)) →
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized B J β τ →
            assignmentCompatible A B J β τ →
              e ∈ openCandidate β →
                e ∈ A →
                  e ∈ prefixFixedSupport β) →
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
                          (β ≠ β' ∨ τ ≠ τ') →
                            (∃ e,
                              e ∈ τ.2.2 ∧
                                selectedPresentSibling
                                  ((A \ τ.2.2) ∪
                                    (B ∪ redSupport β J))
                                  β τ e) ∨
                            (∃ e,
                              e ∈ τ'.2.2 ∧
                                selectedPresentSibling
                                  ((A \ τ'.2.2) ∪
                                    (B ∪ redSupport β' J))
                                  β' τ' e)) →
      ∃ scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        (∀ A β τ,
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                (τ.1 \ (B ∪ redSupport β J)) ⊆ A →
                  Disjoint (τ.2.1 \ τ.2.2) A →
                    scanTranscript
                        ((A \ τ.2.2) ∪ (B ∪ redSupport β J)) =
                      some τ) ∧
        (∀ A β τ,
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                τ.1 ⊆ A →
                  Disjoint τ.2.1 A →
                (∀ e,
                  e ∈ terminal →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)) →
                  scanTranscript A = some τ) ∧
        ∀ A β β' τ τ',
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
                              β = β' ∧ τ = τ' := by
-- BODY
  classical
  intro n m p ε I hist recorded terminal order BranchLabel RedLabel B J
    blueTrace redSupport transcriptLabels cellRealized
    assignmentCompatible scanTranscript witness
    dependencySet stagedOpen touched sameColorClosed preTerminalRecorded
    prefixBefore prefixFixedSupport openCandidate selectedPresentSibling
    horderNodup horderTerminal _hrecordedUniverse _hterminalUniverse
    _hterminalNotRecorded _hprefixSample hrealizedLabel hgeometry
    hcompatForward hwitnessTerminal hwitnessPresent hwitnessAbsent
    hreadClassified hdependenciesPast hexactReadStability
    hdeterministicOutput hprefixBeforeTerminal hprefixSafety hbranchFunctional
    hsiblingSelected hprefixCellGeometry
    hsiblingData hfixedSupportExhaustion hfirstMismatch
  let blueCoord :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl _ => False
      | Sum.inr _ => True
  refine ⟨scanTranscript, ?_, ?_, ?_⟩
  · intro A β τ hA hτ hreal hpresentResidual habsentResidual
    rcases hgeometry β τ hτ hreal with
      ⟨_hRsub, _hRnotBlue, hPresentTerminal, hAbsentTerminal, hDisjoint,
        hFixedSubset, _hBlueTrace, hSelectedSubset⟩
    have hscanPackage :=
      FixedSetHistoryCellRISIRevealOrderScanConstruction
        (terminal := terminal) (order := order)
        (present := fun τ =>
          τ.1)
        (absent := fun τ =>
          τ.2.1)
        (selected := fun τ =>
          τ.2.2)
        (fixedSupport := fun _ =>
          B ∪ redSupport β J)
        (dependencySet := fun τ e =>
          dependencySet β τ e)
        (stagedOpen := stagedOpen) (touched := touched)
        (sameColorClosed := sameColorClosed)
        (preTerminalRecorded := preTerminalRecorded)
        (branchOfAssignment := fun _ => β)
        (scanTranscript := scanTranscript)
        (witness := witness β τ) (β := β) (τ := τ)
        (hreadClassified β τ hτ hreal)
        (hdependenciesPast β τ hτ hreal)
        (hexactReadStability β τ hτ hreal)
        (by
          intro A hA htests
          exact ⟨rfl, hdeterministicOutput β τ hτ hreal A hA htests⟩)
        horderNodup horderTerminal hPresentTerminal hAbsentTerminal
        hFixedSubset hSelectedSubset hDisjoint
        (hwitnessPresent β τ hτ hreal)
        (hwitnessAbsent β τ hτ hreal)
    have hresidual :=
      FixedSetHistoryCellRISIResidualScanStability
        (terminal := terminal) (order := order)
        (present := fun τ =>
          τ.1)
        (absent := fun τ =>
          τ.2.1)
        (selected := fun τ =>
          τ.2.2)
        (fixedSupport := fun _ =>
          B ∪ redSupport β J)
        (dependencySet := fun τ e =>
          dependencySet β τ e)
        (stagedOpen := stagedOpen) (touched := touched)
        (sameColorClosed := sameColorClosed)
        (preTerminalRecorded := preTerminalRecorded)
        (branchOfAssignment := fun _ => β)
        (scanTranscript := scanTranscript)
        (witness := witness β τ) (residualAssignment := A)
        (β := β) (τ := τ)
        horderTerminal hPresentTerminal hAbsentTerminal
        (hwitnessTerminal β τ hτ hreal) hA hFixedSubset
        hSelectedSubset hDisjoint
        (hwitnessPresent β τ hτ hreal)
        (hwitnessAbsent β τ hτ hreal) hpresentResidual
        habsentResidual hscanPackage.1 hscanPackage.2.1
        hscanPackage.2.2
    exact hresidual.2.2.2.2
  · intro A β τ hA hτ hreal hPresentInA hAbsentA _hBlueA
    rcases hgeometry β τ hτ hreal with
      ⟨_hRsub, _hRnotBlue, hPresentTerminal, hAbsentTerminal, hDisjoint,
        hFixedSubset, _hBlueTrace, hSelectedSubset⟩
    have hscanPackage :=
      FixedSetHistoryCellRISIRevealOrderScanConstruction
        (terminal := terminal) (order := order)
        (present := fun τ =>
          τ.1)
        (absent := fun τ =>
          τ.2.1)
        (selected := fun τ =>
          τ.2.2)
        (fixedSupport := fun _ =>
          B ∪ redSupport β J)
        (dependencySet := fun τ e =>
          dependencySet β τ e)
        (stagedOpen := stagedOpen) (touched := touched)
        (sameColorClosed := sameColorClosed)
        (preTerminalRecorded := preTerminalRecorded)
        (branchOfAssignment := fun _ => β)
        (scanTranscript := scanTranscript)
        (witness := witness β τ) (β := β) (τ := τ)
        (hreadClassified β τ hτ hreal)
        (hdependenciesPast β τ hτ hreal)
        (hexactReadStability β τ hτ hreal)
        (by
          intro A hA htests
          exact ⟨rfl, hdeterministicOutput β τ hτ hreal A hA htests⟩)
        horderNodup horderTerminal hPresentTerminal hAbsentTerminal
        hFixedSubset hSelectedSubset hDisjoint
        (hwitnessPresent β τ hτ hreal)
        (hwitnessAbsent β τ hτ hreal)
    have htestAgreement :
        ∀ e,
          e ∈ terminal →
            (stagedOpen (witness β τ) e ↔ stagedOpen A e) ∧
            (touched (witness β τ) e ↔ touched A e) ∧
            (sameColorClosed (witness β τ) e ↔ sameColorClosed A e) ∧
            (preTerminalRecorded (witness β τ) e ↔
              preTerminalRecorded A e) := by
      intro e he
      exact
        hscanPackage.2.1 A hA e he (by
          intro c hc
          have hcovered : c ∈ τ.1 ∪ τ.2.1 :=
            (hscanPackage.1 e he) hc
          rcases Finset.mem_union.mp hcovered with hcPresent | hcAbsent
          · have hcWitness : c ∈ witness β τ :=
              hwitnessPresent β τ hτ hreal c hcPresent
            have hcA : c ∈ A := hPresentInA hcPresent
            exact ⟨fun _ => hcA, fun _ => hcWitness⟩
          · have hcWitness : c ∉ witness β τ :=
              hwitnessAbsent β τ hτ hreal c hcAbsent
            have hcA : c ∉ A := by
              intro hcA
              exact (Finset.disjoint_left.mp hAbsentA hcAbsent) hcA
            exact
              ⟨fun hw => False.elim (hcWitness hw),
                fun hA' => False.elim (hcA hA')⟩)
    exact (hscanPackage.2.2 A hA htestAgreement).2
  · intro A β β' τ τ' hA hτ hτ' hreal hreal' hpresentResidual
      habsentResidual hpresentResidual' habsentResidual' hcompat hcompat'
    have hprune :
        ∀ A₀ β₀ τ₀ e,
          A₀ ⊆ terminal →
            cellRealized B J β₀ τ₀ →
              e ∈ τ₀.2.2 →
                selectedPresentSibling A₀ β₀ τ₀ e →
                  ∀ β₁ τ₁,
                    cellRealized B J β₁ τ₁ →
                      ¬ assignmentCompatible A₀ B J β₁ τ₁ := by
      intro A₀ β₀ τ₀ e hA₀ hreal₀ heSelected hsibling β₁ τ₁
        hreal₁ hcompat₁
      rcases hprefixCellGeometry β₀ τ₀ hreal₀ with
        ⟨hfixedSubset, hpresentAbsent, hselectedAbsent,
          hselectedOpen⟩
      rcases hsiblingData A₀ β₀ τ₀ e hA₀ hreal₀ heSelected hsibling with
        ⟨heA, hblueA⟩
      have hblueA₁ :
          ∀ c,
            c ∈ terminal →
              blueCoord c →
                (c ∈ blueTrace β₁ ↔ c ∈ A₀) := by
        intro c hc hblue
        exact
          (hcompatForward A₀ β₁ τ₁ hA₀
            (hrealizedLabel β₁ τ₁ hreal₁) hreal₁ hcompat₁).2.2
            c hc hblue
      have hβ₁ : β₁ = β₀ := by
        apply hbranchFunctional
        intro c hc hblue
        exact (hblueA₁ c hc hblue).trans ((hblueA c hc hblue).symm)
      have hopen₁ : e ∈ openCandidate β₁ := by
        simpa [hβ₁] using hselectedOpen heSelected
      have hfixed₁ : e ∈ prefixFixedSupport β₁ :=
        hfixedSupportExhaustion A₀ β₁ τ₁ e hA₀ hreal₁ hcompat₁
          hopen₁ heA
      have hfixed₀ : e ∈ prefixFixedSupport β₀ := by
        simpa [hβ₁] using hfixed₁
      have hpresent₀ : e ∈ τ₀.1 := hfixedSubset hfixed₀
      have habsent₀ : e ∈ τ₀.2.1 := hselectedAbsent heSelected
      exact (Finset.disjoint_left.mp hpresentAbsent hpresent₀) habsent₀
    by_contra hnot
    have hmismatch : β ≠ β' ∨ τ ≠ τ' := by
      by_cases hβ : β = β'
      · right
        intro hτeq
        exact hnot ⟨hβ, hτeq⟩
      · exact Or.inl hβ
    have hrecSubset :
        ((A \ τ.2.2) ∪ (B ∪ redSupport β J)) ⊆ terminal := by
      intro c hc
      rcases Finset.mem_union.mp hc with hcA | hfixed
      · exact hA (Finset.mem_sdiff.mp hcA).1
      · rcases hgeometry β τ hτ hreal with
          ⟨_hRsub, _hRnotBlue, hPresentTerminal, _hAbsentTerminal,
            _hDisjoint, hFixedSubset, _hBlueTrace, _hSelectedSubset⟩
        exact hPresentTerminal (hFixedSubset hfixed)
    have hrecSubset' :
        ((A \ τ'.2.2) ∪ (B ∪ redSupport β' J)) ⊆ terminal := by
      intro c hc
      rcases Finset.mem_union.mp hc with hcA | hfixed
      · exact hA (Finset.mem_sdiff.mp hcA).1
      · rcases hgeometry β' τ' hτ' hreal' with
          ⟨_hRsub, _hRnotBlue, hPresentTerminal, _hAbsentTerminal,
            _hDisjoint, hFixedSubset, _hBlueTrace, _hSelectedSubset⟩
        exact hPresentTerminal (hFixedSubset hfixed)
    have hsibling :=
      hfirstMismatch A β β' τ τ' hA hτ hτ' hreal hreal'
        hpresentResidual habsentResidual hpresentResidual'
        habsentResidual' hcompat hcompat' hmismatch
    rcases hsibling with hsibling | hsibling'
    · rcases hsibling with ⟨e, heSelected, hsib⟩
      exact
        (hprune ((A \ τ.2.2) ∪ (B ∪ redSupport β J)) β τ e
          hrecSubset hreal heSelected hsib β τ hreal) hcompat
    · rcases hsibling' with ⟨e, heSelected, hsib⟩
      exact
        (hprune ((A \ τ'.2.2) ∪ (B ∪ redSupport β' J)) β' τ' e
          hrecSubset' hreal' heSelected hsib β' τ' hreal') hcompat'
