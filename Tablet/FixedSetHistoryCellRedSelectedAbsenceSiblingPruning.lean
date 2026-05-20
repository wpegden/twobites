import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellRedSupportLabels

-- [TABLET NODE: FixedSetHistoryCellRedSelectedAbsenceSiblingPruning]

theorem FixedSetHistoryCellRedSelectedAbsenceSiblingPruning :
    ∀ {m : ℕ}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [Fintype BranchLabel]
      (blueTrace :
        BranchLabel →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {RedLabel : Type} [Fintype RedLabel]
      (J : RedLabel)
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (openCandidate :
        BranchLabel →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellRealized :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (branchOfAssignment :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → BranchLabel)
      (scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      (selectedPresentSibling :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop),
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            (match e with
            | Sum.inl _ => False
            | Sum.inr _ => True) →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible A β τ →
                (∀ e,
                  e ∈ terminal →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)) ∧
                  β = branchOfAssignment A ∧
                    scanTranscript A = some τ) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            redSupport β J ⊆ terminal ∧
              B ∪ redSupport β J ⊆ τ.1 ∧
              Disjoint τ.1 τ.2.1 ∧
              τ.2.2 ⊆ τ.2.1 ∧
              τ.2.2 ⊆ openCandidate β) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              e ∈ τ.2.2 →
                selectedPresentSibling A β τ e →
                  e ∈ A ∧
                    (∀ c,
                      c ∈ terminal →
                        (match c with
                        | Sum.inl _ => False
                        | Sum.inr _ => True) →
                          (c ∈ blueTrace β ↔ c ∈ A))) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible A β τ →
                e ∈ openCandidate β →
                  e ∈ A →
                    e ∈ B ∪ redSupport β J) →
      ∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              e ∈ τ.2.2 →
                selectedPresentSibling A β τ e →
                  ∀ (β' : BranchLabel)
                    (τ' :
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
                    τ' ∈ transcriptLabels →
                      cellRealized β' τ' →
                        ¬ assignmentCompatible A β' τ' := by
-- BODY
  classical
  intro m terminal B BranchLabel _ blueTrace transcriptLabels RedLabel _ J
    redSupport openCandidate cellRealized assignmentCompatible
    branchOfAssignment scanTranscript selectedPresentSibling hbranch
    hcompatible hgeometry hsibling hsupport A β τ e hA hτ hreal heZ hsib
    β' τ' hτ' hreal' hcomp
  rcases hsibling A β τ e hA hτ hreal heZ hsib with
    ⟨he_present, hblue_sibling⟩
  rcases hcompatible A β' τ' hA hτ' hreal' hcomp with
    ⟨hblue_compat, _hfunctional⟩
  have hsame_blue :
      ∀ c,
        c ∈ terminal →
          (match c with
          | Sum.inl _ => False
          | Sum.inr _ => True) →
            (c ∈ blueTrace β ↔ c ∈ blueTrace β') := by
    intro c hc hblue
    exact (hblue_sibling c hc hblue).trans (hblue_compat c hc hblue).symm
  have hβ : β = β' := hbranch β β' hsame_blue
  subst β'
  rcases hgeometry β τ hτ hreal with
    ⟨_hR_terminal, hsupport_subset, hdisjoint, hZ_absent, hZ_open⟩
  have he_open : e ∈ openCandidate β := hZ_open heZ
  have he_support : e ∈ B ∪ redSupport β J :=
    hsupport A β τ' e hA hτ' hreal' hcomp he_open he_present
  have he_forced_present : e ∈ τ.1 := hsupport_subset he_support
  have he_forced_absent : e ∈ τ.2.1 := hZ_absent heZ
  exact (Finset.disjoint_left.mp hdisjoint he_forced_present) he_forced_absent
