import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedReleasedCylinderLeafExpansion
import Tablet.FixedSetHistoryCellRedReleasedCylinderUnionMassBound
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellTerminalProductPartition

-- [TABLET NODE: FixedSetHistoryCellRedReleasedCylinderWeightNormalization]

theorem FixedSetHistoryCellRedReleasedCylinderWeightNormalization :
    ∀ {n m uR uB : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
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
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)]
      [DecidablePred
        (fun leaf :
          BranchLabel ×
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) =>
          leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2)]
      [DecidablePred
        (fun e : Sum (Fin m × Fin m) (Fin m × Fin m) =>
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True)],
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      B.card = uB →
      B ⊆ terminal →
          (∀ e,
            e ∈ B →
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            (match e with
            | Sum.inl _ => False
            | Sum.inr _ => True) →
              (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
          β = β') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
          (redSupport β J).card = uR ∧
          redSupport β J ⊆ terminal ∧
          (∀ e,
            e ∈ redSupport β J →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) ∧
          (∀ e,
            e ∈ τ.2.2 →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) ∧
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
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
          openCandidate β ⊆ terminal ∧
          B ∪ redSupport β J ⊆ openCandidate β ∧
          τ.2.2 ⊆ openCandidate β ∧
          (∀ e,
            e ∈ openCandidate β →
              e ∈ τ.1 →
                e ∈ B ∪ redSupport β J)) →
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
                  ∀ (β' : BranchLabel)
                    (τ' :
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
                    τ' ∈ transcriptLabels →
                      cellRealized β' τ' →
                        ¬ assignmentCompatible A β' τ') →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (assignmentCompatible A β τ ∨
                ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ↔
              (τ.1 ⊆ A ∧
                Disjoint (τ.2.1 \ τ.2.2) A ∧
                (∀ e,
                  e ∈ terminal →
                    e ∉ τ.2.2 →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)))) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  (β ≠ β' ∨ τ ≠ τ') →
                    ¬ ((assignmentCompatible A β τ ∨
                        ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ∧
                       (assignmentCompatible A β' τ' ∨
                        ∃ e ∈ τ'.2.2, selectedPresentSibling A β' τ' e))) →
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
                    (e ∈ τ.1 → e ∈ A) ∧
                    (e ∈ τ.2.1 → e ∉ A) ∧
                    ((match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)))) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (∀ e,
                e ∈ terminal →
                  (e ∈ τ.1 → e ∈ A) ∧
                  (e ∈ τ.2.1 → e ∉ A) ∧
                  ((match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                    (e ∈ blueTrace β ↔ e ∈ A))) →
                assignmentCompatible A β τ) →
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
                β = branchOfAssignment A ∧
                  scanTranscript A = some τ) →
      ((Finset.univ :
          Finset
            (BranchLabel ×
              (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))).filter
          (fun leaf =>
            leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2)).sum
          (fun leaf =>
            p ^ leaf.2.1.card *
              ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card))
        ≤
        p ^ uR * p ^ uB := by
-- BODY
  classical
  intro n m uR uB p hist terminal B BranchLabel _ blueTrace
    transcriptLabels RedLabel _ J redSupport openCandidate cellRealized
    assignmentCompatible branchOfAssignment scanTranscript selectedPresentSibling
    _ _ _ hp hp_half hp_dist h_B_card h_B_term h_B_color h_blue_func h_red
    h_open h_sib h_span h_span_disj h_comp_fwd h_comp_rev h_comp_func
  exact le_trans
    (by
      simpa using
        FixedSetHistoryCellRedReleasedCylinderLeafExpansion
          (m := m) (uR := uR) (uB := uB) (p := p)
          terminal B blueTrace transcriptLabels J redSupport cellRealized
          assignmentCompatible selectedPresentSibling hp hp_half h_B_card
          h_B_term h_B_color
          (by
            intro β τ hτ hreal
            rcases h_red β τ hτ hreal with
              ⟨hRcard, hRterm, hRred, _hZred, hPterm, hAterm, hPAdisj,
                hBRsub, hbluegeom, hZsub⟩
            exact
              ⟨hRcard, hRterm, hRred, hPterm, hAterm, hPAdisj,
                hBRsub, hbluegeom, hZsub⟩)
          h_span h_span_disj)
    (by
      simpa using
        FixedSetHistoryCellRedReleasedCylinderUnionMassBound
          (m := m) (uR := uR) (uB := uB) (p := p)
          terminal B blueTrace transcriptLabels J redSupport cellRealized
          hp hp_half h_B_card h_B_term h_B_color h_blue_func h_red)
