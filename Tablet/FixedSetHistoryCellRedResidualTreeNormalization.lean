import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedResidualTreeNormalization]

theorem FixedSetHistoryCellRedResidualTreeNormalization :
    ∀ {m uR uB : ℕ} {a : ℝ}
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [Fintype BranchLabel]
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {RedLabel ResidualLeaf : Type} [Fintype ResidualLeaf]
      [DecidableEq ResidualLeaf]
      (J : RedLabel)
      (redSupport :
        BranchLabel →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
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
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)],
      B.card = uB →
      B ⊆ terminal →
      (∀ e,
        e ∈ B →
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True) →
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
          τ.2.2 ⊆ τ.2.1 ∧
          max 0 (a - (uR : ℝ) - (uB : ℝ)) ≤ ((τ.2.2).card : ℝ)) →
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
      ∃ residualCellMass :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ,
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => residualCellMass β τ))
          ≤ 1 ∧
          (∀ (β : BranchLabel)
            (τ :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
            τ ∈ transcriptLabels →
              cellRealized β τ →
                0 ≤ residualCellMass β τ) ∧
      ∀ (β : BranchLabel)
            (τ :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
            τ ∈ transcriptLabels →
              cellRealized β τ →
                residualCellMass β τ = residualLeafMass (residualLeaf β τ) := by
-- BODY
  classical
  intro m uR uB a terminal B BranchLabel _ transcriptLabels RedLabel
    ResidualLeaf _ _ J redSupport cellRealized residualLeaf residualLeafMass _
    _hB_card _hB_subset _hB_blue _hcell_geometry hleaf_nonneg hleaf_sum
    hleaf_inj
  refine ⟨fun β τ => residualLeafMass (residualLeaf β τ), ?_, ?_, ?_⟩
  · let cells :
        Finset
          (BranchLabel ×
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))) :=
        ((Finset.univ : Finset BranchLabel).product transcriptLabels).filter
          (fun c => cellRealized c.1 c.2)
    have hsum_cells :
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => residualLeafMass (residualLeaf β τ)))
          =
          cells.sum
            (fun c => residualLeafMass (residualLeaf c.1 c.2)) := by
      simp [cells, Finset.sum_product, Finset.sum_filter]
    have hsum_image :
        cells.sum (fun c => residualLeafMass (residualLeaf c.1 c.2))
          =
          (cells.image (fun c => residualLeaf c.1 c.2)).sum residualLeafMass := by
      rw [Finset.sum_image]
      intro c hc d hd hleaf_eq
      have hc_mem :
          c.2 ∈ transcriptLabels := by
        have hprod := (Finset.mem_filter.mp hc).1
        exact (Finset.mem_product.mp hprod).2
      have hd_mem :
          d.2 ∈ transcriptLabels := by
        have hprod := (Finset.mem_filter.mp hd).1
        exact (Finset.mem_product.mp hprod).2
      have hc_real : cellRealized c.1 c.2 :=
        (Finset.mem_filter.mp hc).2
      have hd_real : cellRealized d.1 d.2 :=
        (Finset.mem_filter.mp hd).2
      rcases hleaf_inj c.1 d.1 c.2 d.2 hc_mem hd_mem hc_real hd_real
          hleaf_eq with
        ⟨hβ, hτ⟩
      cases c
      cases d
      simp_all
    have hsubset :
        cells.image (fun c => residualLeaf c.1 c.2) ⊆
          (Finset.univ : Finset ResidualLeaf) := by
      intro leaf _
      exact Finset.mem_univ leaf
    have hnonneg_extra :
        ∀ leaf ∈ (Finset.univ : Finset ResidualLeaf),
          leaf ∉ cells.image (fun c => residualLeaf c.1 c.2) →
            0 ≤ residualLeafMass leaf := by
      intro leaf _ _
      exact hleaf_nonneg leaf
    calc
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => residualLeafMass (residualLeaf β τ)))
          =
          cells.sum
            (fun c => residualLeafMass (residualLeaf c.1 c.2)) := hsum_cells
      _ =
          (cells.image (fun c => residualLeaf c.1 c.2)).sum
            residualLeafMass := hsum_image
      _ ≤
          (Finset.univ : Finset ResidualLeaf).sum residualLeafMass :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg_extra
      _ ≤ 1 := hleaf_sum
  · intro β τ _hτ _hreal
    exact hleaf_nonneg (residualLeaf β τ)
  · intro β τ _hτ _hreal
    rfl
