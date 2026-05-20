import Tablet.FixedSetHistoryCellFixedBJResidualOverlapConsistency
import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedPrefixScanInvariant

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualScanInterface]

theorem FixedSetHistoryCellFixedBJResidualScanInterface :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (order : List Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (fixedSupport : BranchLabel → Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      (assignmentCompatible : Finset Coord → BranchLabel → Transcript → Prop),
      order.Nodup →
      order.toFinset = terminal →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            fixedSupport β τ ⊆ present τ ∧
            present τ ⊆ terminal ∧
            absent τ ⊆ terminal ∧
            Disjoint (present τ) (absent τ) ∧
            selected τ ⊆ absent τ) →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible A β τ →
                present τ ⊆ A ∧
                Disjoint (absent τ \ selected τ) A) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  assignmentCompatible A β τ →
                    assignmentCompatible A β' τ' →
                      β = β' ∧ τ = τ') →
      (∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              fixedSupport β τ ⊆ present τ →
                (present τ \ fixedSupport β τ) ⊆ A →
                  Disjoint (absent τ \ selected τ) A →
                    assignmentCompatible
                      ((A \ selected τ) ∪ fixedSupport β τ) β τ) →
      (∀ A β β' τ τ',
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  assignmentCompatible
                    ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                  assignmentCompatible
                    ((A \ selected τ') ∪ fixedSupport β' τ') β' τ' →
                    β = β' ∧ τ = τ') →
      ∃ residualScan : Finset Coord → Option (BranchLabel × Transcript),
        ∃ reconstructedScan :
          Finset Coord → Option (BranchLabel × Transcript),
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  reconstructedScan A = some (β, τ) →
                    assignmentCompatible A β τ) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  assignmentCompatible A β τ →
                    reconstructedScan A = some (β, τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  fixedSupport β τ ⊆ present τ →
                    (present τ \ fixedSupport β τ) ⊆ A →
                      Disjoint (absent τ \ selected τ) A →
                        residualScan A =
                          reconstructedScan
                            ((A \ selected τ) ∪ fixedSupport β τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  fixedSupport β τ ⊆ present τ →
                    (present τ \ fixedSupport β τ) ⊆ A →
                      Disjoint (absent τ \ selected τ) A →
                        reconstructedScan
                            ((A \ selected τ) ∪ fixedSupport β τ) =
                          some (β, τ)) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  residualScan A = some (β, τ) →
                    assignmentCompatible
                      ((A \ selected τ) ∪ fixedSupport β τ) β τ) ∧
          (∀ A β τ,
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  assignmentCompatible
                    ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                    residualScan A = some (β, τ)) ∧
          ∀ A β β' τ τ',
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                τ' ∈ transcriptLabels →
                  cellRealized β τ →
                    cellRealized β' τ' →
                      residualScan A = some (β, τ) →
                        residualScan A = some (β', τ') →
                          β = β' ∧ τ = τ' := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ terminal order transcriptLabels
    present absent selected fixedSupport cellRealized assignmentCompatible
    _horder_nodup _horder_terminal hrealized_geometry _hcompat_forward
    hcompat_inj hresidual_complete hresidual_single_owner
  let completeCandidate (A : Finset Coord) (x : BranchLabel × Transcript) :
      Prop :=
    x.2 ∈ transcriptLabels ∧
      cellRealized x.1 x.2 ∧ assignmentCompatible A x.1 x.2
  let reconstructedScan :
      Finset Coord → Option (BranchLabel × Transcript) :=
    fun A =>
      if h : ∃ x : BranchLabel × Transcript, completeCandidate A x then
        some (Classical.choose h)
      else
        none
  let residualCandidate (A : Finset Coord) (x : BranchLabel × Transcript) :
      Prop :=
    x.2 ∈ transcriptLabels ∧
      cellRealized x.1 x.2 ∧
        assignmentCompatible ((A \ selected x.2) ∪ fixedSupport x.1 x.2)
          x.1 x.2
  let residualScan :
      Finset Coord → Option (BranchLabel × Transcript) :=
    fun A =>
      if h : ∃ x : BranchLabel × Transcript, residualCandidate A x then
        some (Classical.choose h)
      else
        none
  have hreconstructed_of_compat :
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible A β τ →
                reconstructedScan A = some (β, τ) := by
    intro A β τ hA hτ hreal hcompat
    let x : BranchLabel × Transcript := (β, τ)
    have hexists : ∃ y : BranchLabel × Transcript, completeCandidate A y :=
      ⟨x, hτ, hreal, hcompat⟩
    have hspec : completeCandidate A (Classical.choose hexists) :=
      Classical.choose_spec hexists
    have hchosen : Classical.choose hexists = x := by
      have hpair :=
        hcompat_inj A (Classical.choose hexists).1 β
          (Classical.choose hexists).2 τ hA hspec.1 hτ hspec.2.1
          hreal hspec.2.2 hcompat
      exact Prod.ext hpair.1 hpair.2
    dsimp [reconstructedScan]
    rw [dif_pos hexists]
    exact congrArg some hchosen
  have hcompat_of_reconstructed :
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              reconstructedScan A = some (β, τ) →
                assignmentCompatible A β τ := by
    intro A β τ _hA _hτ _hreal hscan
    by_cases hexists :
        ∃ x : BranchLabel × Transcript, completeCandidate A x
    · dsimp [reconstructedScan] at hscan
      rw [dif_pos hexists] at hscan
      injection hscan with hchosen
      have hspec : completeCandidate A (Classical.choose hexists) :=
        Classical.choose_spec hexists
      simpa [completeCandidate, hchosen] using hspec.2.2
    · dsimp [reconstructedScan] at hscan
      rw [dif_neg hexists] at hscan
      cases hscan
  have hresidual_of_compat :
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible
                ((A \ selected τ) ∪ fixedSupport β τ) β τ →
                residualScan A = some (β, τ) := by
    intro A β τ hA hτ hreal hcompat
    let x : BranchLabel × Transcript := (β, τ)
    have hexists : ∃ y : BranchLabel × Transcript, residualCandidate A y :=
      ⟨x, hτ, hreal, hcompat⟩
    have hspec : residualCandidate A (Classical.choose hexists) :=
      Classical.choose_spec hexists
    have hchosen : Classical.choose hexists = x := by
      have hpair :=
        hresidual_single_owner A (Classical.choose hexists).1 β
          (Classical.choose hexists).2 τ hA hspec.1 hτ hspec.2.1
          hreal hspec.2.2 hcompat
      exact Prod.ext hpair.1 hpair.2
    dsimp [residualScan]
    rw [dif_pos hexists]
    exact congrArg some hchosen
  have hcompat_of_residual :
      ∀ A β τ,
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              residualScan A = some (β, τ) →
                assignmentCompatible
                  ((A \ selected τ) ∪ fixedSupport β τ) β τ := by
    intro A β τ _hA _hτ _hreal hscan
    by_cases hexists :
        ∃ x : BranchLabel × Transcript, residualCandidate A x
    · dsimp [residualScan] at hscan
      rw [dif_pos hexists] at hscan
      injection hscan with hchosen
      have hspec : residualCandidate A (Classical.choose hexists) :=
        Classical.choose_spec hexists
      simpa [residualCandidate, hchosen] using hspec.2.2
    · dsimp [residualScan] at hscan
      rw [dif_neg hexists] at hscan
      cases hscan
  refine
    ⟨residualScan, reconstructedScan, hcompat_of_reconstructed,
      hreconstructed_of_compat, ?_, ?_, hcompat_of_residual,
      hresidual_of_compat, ?_⟩
  · intro A β τ hA hτ hreal hfixed hpresent_res habsent_res
    have hcompat :
        assignmentCompatible ((A \ selected τ) ∪ fixedSupport β τ) β τ :=
      hresidual_complete A β τ hA hτ hreal hfixed hpresent_res habsent_res
    have hrec_subset :
        ((A \ selected τ) ∪ fixedSupport β τ) ⊆ terminal := by
      intro c hc
      rcases Finset.mem_union.mp hc with hcA | hcfixed
      · exact hA (Finset.mem_sdiff.mp hcA).1
      · exact (hrealized_geometry β τ hτ hreal).2.1 (hfixed hcfixed)
    have hres :
        residualScan A = some (β, τ) :=
      hresidual_of_compat A β τ hA hτ hreal hcompat
    have hrec :
        reconstructedScan ((A \ selected τ) ∪ fixedSupport β τ) =
          some (β, τ) :=
      hreconstructed_of_compat ((A \ selected τ) ∪ fixedSupport β τ) β τ
        hrec_subset hτ hreal hcompat
    exact hres.trans hrec.symm
  · intro A β τ hA hτ hreal hfixed hpresent_res habsent_res
    have hcompat :
        assignmentCompatible ((A \ selected τ) ∪ fixedSupport β τ) β τ :=
      hresidual_complete A β τ hA hτ hreal hfixed hpresent_res habsent_res
    have hrec_subset :
        ((A \ selected τ) ∪ fixedSupport β τ) ⊆ terminal := by
      intro c hc
      rcases Finset.mem_union.mp hc with hcA | hcfixed
      · exact hA (Finset.mem_sdiff.mp hcA).1
      · exact (hrealized_geometry β τ hτ hreal).2.1 (hfixed hcfixed)
    exact
      hreconstructed_of_compat ((A \ selected τ) ∪ fixedSupport β τ) β τ
        hrec_subset hτ hreal hcompat
  · intro A β β' τ τ' _hA _hτ _hτ' _hreal _hreal' hscan hscan'
    have hsome : some (β, τ) = some (β', τ') := hscan.symm.trans hscan'
    injection hsome with hpair
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
