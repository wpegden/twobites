import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness

-- [TABLET NODE: FixedSetHistoryCellRedCompatibleAssignmentDisjointness]

theorem FixedSetHistoryCellRedCompatibleAssignmentDisjointness :
    ∀ {m : ℕ} {BranchLabel Transcript : Type}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel → Transcript → Prop)
      (selectedPresentSibling :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel → Transcript →
            Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
      (branchOfAssignment :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel)
      (scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option Transcript),
      (∀ A β τ e,
        A ⊆ terminal →
          cellRealized β τ →
            selectedPresentSibling A β τ e →
              ∀ β' τ',
                cellRealized β' τ' →
                  ¬ assignmentCompatible A β' τ') →
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              β = branchOfAssignment A ∧
                scanTranscript A = some τ) →
      ∀ A β β' τ τ',
        A ⊆ terminal →
          cellRealized β τ →
            cellRealized β' τ' →
              assignmentCompatible A β τ →
                assignmentCompatible A β' τ' →
                  (∀ e, ¬ selectedPresentSibling A β τ e) ∧
                    (∀ e, ¬ selectedPresentSibling A β' τ' e) ∧
                      β = β' ∧ τ = τ' := by
-- BODY
  intro m BranchLabel Transcript terminal cellRealized assignmentCompatible
    selectedPresentSibling branchOfAssignment scanTranscript hprune
    hfunctional A β β' τ τ' hA hreal hreal' hcomp hcomp'
  have hno_sibling : ∀ e, ¬ selectedPresentSibling A β τ e := by
    intro e hsibling
    exact (hprune A β τ e hA hreal hsibling β τ hreal) hcomp
  have hno_sibling' : ∀ e, ¬ selectedPresentSibling A β' τ' e := by
    intro e hsibling
    exact (hprune A β' τ' e hA hreal' hsibling β' τ' hreal') hcomp'
  have hunique :=
    FixedSetHistoryCellRedFunctionalScanDisjointness terminal cellRealized
      assignmentCompatible branchOfAssignment scanTranscript hfunctional
      A β β' τ τ' hA hreal hreal' hcomp hcomp'
  exact ⟨hno_sibling, hno_sibling', hunique⟩
