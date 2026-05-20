import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedResidualTreeNormalization
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellTerminalProductPartition

-- [TABLET NODE: FixedSetHistoryCellRedCompatibleCompletionBlocks]

theorem FixedSetHistoryCellRedCompatibleCompletionBlocks :
    ∀ {n m uR uB : ℕ} {p a : ℝ}
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
      {ResidualLeaf : Type} [Fintype ResidualLeaf] [DecidableEq ResidualLeaf]
      (J : RedLabel)
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellWeight :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ)
      (cellRealized :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (residualLeaf :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ResidualLeaf)
      (residualLeafMass : ResidualLeaf → ℝ)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)],
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
                  assignmentCompatible A β τ →
                    assignmentCompatible A β' τ' →
                      β = β' ∧ τ = τ') →
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
          τ.2.2 ⊆ τ.2.1 ∧
          max 0 (a - (uR : ℝ) - (uB : ℝ)) ≤ ((τ.2.2).card : ℝ)) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          0 ≤ cellWeight β τ) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          ¬ cellRealized β τ →
            cellWeight β τ = 0) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellWeight β τ
            ≤
            p ^ τ.1.card *
              ((1 : ℝ) - p) ^ τ.2.1.card) →
      (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) →
      (Finset.univ : Finset ResidualLeaf).sum residualLeafMass ≤ 1 →
      (∀ (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          τ' ∈ transcriptLabels →
            cellRealized β τ →
              cellRealized β' τ' →
                residualLeaf β τ = residualLeaf β' τ' →
                  β = β' ∧ τ = τ') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ τ.1.card *
                ((1 : ℝ) - p) ^ τ.2.1.card
              ≤
              p ^ uR * p ^ uB *
                  Real.rpow ((1 : ℝ) - p)
                    (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
                residualLeafMass (residualLeaf β τ)) →
      ∃ completionBlockMass :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ,
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => completionBlockMass β τ))
          ≤ 1 ∧
          (∀ (β : BranchLabel)
            (τ :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
            τ ∈ transcriptLabels →
              cellRealized β τ →
                0 ≤ completionBlockMass β τ) ∧
          ∀ (β : BranchLabel)
            (τ :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
            τ ∈ transcriptLabels →
              cellRealized β τ →
                cellWeight β τ
                  ≤
                  p ^ uR * p ^ uB *
                      Real.rpow ((1 : ℝ) - p)
                        (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
                    completionBlockMass β τ := by
-- BODY
  classical
  intro n m uR uB p a hist terminal B BranchLabel _ blueTrace
    transcriptLabels RedLabel _ ResidualLeaf _ _ J redSupport cellWeight
    cellRealized residualLeaf residualLeafMass assignmentCompatible _
    hp_nonneg hp_le_half hproductLaw hB_card hB_subset hB_blue
    hblueTrace_functional hforward hconverse hscan_disjoint hcell_geometry
    hweight_nonneg hzero hcell_cyl hleaf_nonneg hleaf_sum hleaf_inj hcyl_leaf
  have hcell_geometry' :
      ∀ (β : BranchLabel)
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
          τ.1 ⊆ terminal ∧
          τ.2.1 ⊆ terminal ∧
          Disjoint τ.1 τ.2.1 ∧
          B ∪ redSupport β J ⊆ τ.1 ∧
          τ.2.2 ⊆ τ.2.1 ∧
          max 0 (a - (uR : ℝ) - (uB : ℝ)) ≤ ((τ.2.2).card : ℝ) := by
    intro β τ hτ hreal
    rcases hcell_geometry β τ hτ hreal with
      ⟨hR_card, hR_subset, hR_color, hP_subset, hA_subset, hPA_disjoint,
        hmandatory, _hblue_trace, hZ_subset, hZ_large⟩
    exact
      ⟨hR_card, hR_subset, hR_color, hP_subset, hA_subset, hPA_disjoint,
        hmandatory, hZ_subset, hZ_large⟩
  rcases
      FixedSetHistoryCellRedResidualTreeNormalization
        (m := m) (uR := uR) (uB := uB) (a := a)
        terminal B transcriptLabels J redSupport cellRealized residualLeaf
        residualLeafMass hB_card hB_subset hB_blue hcell_geometry'
        hleaf_nonneg hleaf_sum hleaf_inj with
    ⟨residualCellMass, hresidual_sum, hresidual_nonneg, hresidual_eq⟩
  refine ⟨residualCellMass, hresidual_sum, hresidual_nonneg, ?_⟩
  intro β τ hτ hreal
  calc
    cellWeight β τ
        ≤ p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card :=
          hcell_cyl β τ hτ
    _ ≤
        p ^ uR * p ^ uB *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
          residualLeafMass (residualLeaf β τ) :=
          hcyl_leaf β τ hτ hreal
    _ =
        p ^ uR * p ^ uB *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
          residualCellMass β τ := by
          rw [hresidual_eq β τ hτ hreal]
