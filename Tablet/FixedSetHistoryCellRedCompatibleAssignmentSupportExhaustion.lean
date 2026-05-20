import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedSupportLabels
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteStagedOpenPairs

-- [TABLET NODE: FixedSetHistoryCellRedCompatibleAssignmentSupportExhaustion]

theorem FixedSetHistoryCellRedCompatibleAssignmentSupportExhaustion :
    ∀ {n m : ℕ} {p ε : ℝ}
      (I : Finset (Fin n))
      (target : TwoBiteSample n m p → Prop)
      (terminal B :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [Fintype BranchLabel]
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
      (assignmentSample :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          TwoBiteSample n m p)
      (cellEvent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          RedLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          TwoBiteSample n m p → Prop)
      [∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue (assignmentSample A) e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False)]
      [∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue (assignmentSample A) e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True)],
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
                target (assignmentSample A) ∧
                  cellEvent B J β τ (assignmentSample A) ∧
                  B =
                    (TwoBiteStagedOpenPairs (assignmentSample A) ε I).filter
                      (fun e =>
                        TwoBiteEdgeCoordinateValue (assignmentSample A) e ∧
                          match e with
                          | Sum.inl _ => False
                          | Sum.inr _ => True) ∧
                  redSupport β J =
                    (TwoBiteStagedOpenPairs (assignmentSample A) ε I).filter
                      (fun e =>
                        TwoBiteEdgeCoordinateValue (assignmentSample A) e ∧
                          match e with
                          | Sum.inl _ => True
                          | Sum.inr _ => False)) →
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
                    e ∈ TwoBiteStagedOpenPairs (assignmentSample A) ε I ∧
                      TwoBiteEdgeCoordinateValue (assignmentSample A) e) →
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
              assignmentCompatible A β τ →
                e ∈ openCandidate β →
                  e ∈ A →
                    e ∈ B ∪ redSupport β J := by
-- BODY
  classical
  intro n m p ε I target terminal B BranchLabel _ transcriptLabels RedLabel _
    J redSupport openCandidate cellRealized assignmentCompatible
    assignmentSample cellEvent _ _ hreconstruct hcandidate A β τ e hA hτ
    hreal hcomp he_open he_present
  rcases hreconstruct A β τ hA hτ hreal hcomp with
    ⟨_htarget, _hcell, hB_support, hR_support⟩
  rcases hcandidate A β τ e hA hτ hreal hcomp he_open he_present with
    ⟨he_staged, he_value⟩
  cases e with
  | inl eR =>
      exact Finset.mem_union_right B (by
        rw [hR_support]
        simp [he_staged, he_value])
  | inr eB =>
      exact Finset.mem_union_left (redSupport β J) (by
        rw [hB_support]
        simp [he_staged, he_value])
