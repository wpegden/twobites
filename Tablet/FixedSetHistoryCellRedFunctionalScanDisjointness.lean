import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedFunctionalScanDisjointness]

theorem FixedSetHistoryCellRedFunctionalScanDisjointness :
    ∀ {m : ℕ} {BranchLabel Transcript : Type}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel → Transcript → Prop)
      (branchOfAssignment :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel)
      (scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option Transcript),
      (∀ A β τ,
        A ⊆ terminal →
          cellRealized β τ →
            assignmentCompatible A β τ →
              β = branchOfAssignment A ∧ scanTranscript A = some τ) →
      ∀ A β β' τ τ',
        A ⊆ terminal →
          cellRealized β τ →
          cellRealized β' τ' →
          assignmentCompatible A β τ →
          assignmentCompatible A β' τ' →
            β = β' ∧ τ = τ' := by
-- BODY
  intro m BranchLabel Transcript terminal cellRealized assignmentCompatible
    branchOfAssignment scanTranscript hfunctional A β β' τ τ' hA hreal
    hreal' hcomp hcomp'
  rcases hfunctional A β τ hA hreal hcomp with ⟨hβ, hτ⟩
  rcases hfunctional A β' τ' hA hreal' hcomp' with ⟨hβ', hτ'⟩
  constructor
  · exact hβ.trans hβ'.symm
  · simpa [hτ] using hτ'
