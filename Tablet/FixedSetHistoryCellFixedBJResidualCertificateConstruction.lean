import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualCertificateConstruction]

theorem FixedSetHistoryCellFixedBJResidualCertificateConstruction :
    ∀ {Coord BranchLabel Transcript ResidualLeaf : Type}
      [DecidableEq Coord] [Fintype BranchLabel] [DecidableEq Transcript]
      [Fintype ResidualLeaf] [DecidableEq ResidualLeaf]
      {uR uB : ℕ} {p a : ℝ}
      (terminal B : Finset Coord)
      (order : List Coord)
      (transcriptLabels : Finset Transcript)
      (blueCoord : Coord → Prop)
      (blueTrace : BranchLabel → Finset Coord)
      (redSupport : BranchLabel → Finset Coord)
      (present absent selected : Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      [∀ β : BranchLabel, DecidablePred (fun τ => cellRealized β τ)]
      (residualLeaf : BranchLabel → Transcript → ResidualLeaf)
      (residualLeafMass : ResidualLeaf → ℝ),
      order.Nodup →
      order.toFinset = terminal →
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      B.card = uB →
      B ⊆ terminal →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            (redSupport β).card = uR ∧
            redSupport β ⊆ terminal ∧
            Disjoint B (redSupport β) ∧
            present τ ⊆ terminal ∧
            absent τ ⊆ terminal ∧
            Disjoint (present τ) (absent τ) ∧
            B ∪ redSupport β ⊆ present τ ∧
            (∀ e,
              e ∈ terminal →
                blueCoord e →
                  (e ∈ blueTrace β ↔ e ∈ present τ) ∧
                  (e ∉ blueTrace β ↔ e ∈ absent τ)) ∧
            selected τ ⊆ absent τ ∧
            max 0 (a - (uR : ℝ) - (uB : ℝ))
              ≤ ((selected τ).card : ℝ)) →
      (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) →
      (Finset.univ : Finset ResidualLeaf).sum residualLeafMass ≤ 1 →
      (∀ β β' : BranchLabel,
        ∀ τ τ',
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  residualLeaf β τ = residualLeaf β' τ' →
                    β = β' ∧ τ = τ') →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ ((present τ).card - uR - uB) *
                ((1 : ℝ) - p) ^ ((absent τ).card - (selected τ).card)
              ≤ residualLeafMass (residualLeaf β τ)) →
      ∃ residualMass : BranchLabel → Transcript → ℝ,
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized β τ →
              0 ≤ residualMass β τ) ∧
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => residualMass β τ))
          ≤ 1 ∧
        ∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized β τ →
              p ^ ((present τ).card - uR - uB) *
                  ((1 : ℝ) - p) ^ ((absent τ).card - (selected τ).card)
                ≤ residualMass β τ := by
-- BODY
  classical
  intro Coord BranchLabel Transcript ResidualLeaf _hCoord _hBranch _hTranscript
    _hResidualLeaf _hResidualLeafEq uR uB p a terminal B order
    transcriptLabels blueCoord blueTrace redSupport present absent selected
    cellRealized _hDecReal residualLeaf residualLeafMass _horder _horder_set
    _hp _hp_half _hBcard _hBterm _hgeom hleaf_nonneg hleaf_sum hleaf_inj
    hleaf_dom
  refine ⟨fun β τ => residualLeafMass (residualLeaf β τ), ?_, ?_, ?_⟩
  · intro β τ _hτ _hreal
    exact hleaf_nonneg (residualLeaf β τ)
  · let cells : Finset (BranchLabel × Transcript) :=
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
          (cells.image (fun c => residualLeaf c.1 c.2)).sum
            residualLeafMass := by
      rw [Finset.sum_image]
      intro c hc d hd hleaf_eq
      have hc_mem : c.2 ∈ transcriptLabels := by
        have hprod := (Finset.mem_filter.mp hc).1
        exact (Finset.mem_product.mp hprod).2
      have hd_mem : d.2 ∈ transcriptLabels := by
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
      intro leaf _hmem
      exact Finset.mem_univ leaf
    have hnonneg_extra :
        ∀ leaf ∈ (Finset.univ : Finset ResidualLeaf),
          leaf ∉ cells.image (fun c => residualLeaf c.1 c.2) →
            0 ≤ residualLeafMass leaf := by
      intro leaf _huniv _hnot
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
      _ ≤ (Finset.univ : Finset ResidualLeaf).sum residualLeafMass :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg_extra
      _ ≤ 1 := hleaf_sum
  · intro β τ hτ hreal
    exact hleaf_dom β τ hτ hreal
