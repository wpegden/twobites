import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.FixedSetHistoryCellFixedBJResidualCertificateConstruction
import Tablet.FixedSetHistoryCellRedTermwiseCylinderDomination

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualProductTreePacking]

theorem FixedSetHistoryCellFixedBJResidualProductTreePacking :
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
        (∀ β τ, τ ∈ transcriptLabels → 0 ≤ residualMass β τ) ∧
        (Finset.univ : Finset BranchLabel).sum
            (fun β => transcriptLabels.sum (fun τ => residualMass β τ))
          ≤ 1 ∧
        ∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized β τ →
              p ^ (present τ).card *
                  ((1 : ℝ) - p) ^ (absent τ).card
                ≤
                p ^ uR * p ^ uB *
                    Real.rpow ((1 : ℝ) - p)
                      (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
                  residualMass β τ := by
-- BODY
  classical
  intro Coord BranchLabel Transcript ResidualLeaf hCoord hBranch hTranscript
    hResidualLeaf hResidualLeafEq uR uB p a terminal B order transcriptLabels
    blueCoord blueTrace redSupport present absent selected cellRealized
    hDecReal residualLeaf residualLeafMass horder horder_set hp hp_half hBcard
    hBterm hgeom hleaf_nonneg hleaf_sum hleaf_inj hleaf_dom
  obtain ⟨residualMass, hres_nonneg, hres_sum, hres_dom⟩ :=
    FixedSetHistoryCellFixedBJResidualCertificateConstruction
      terminal B order transcriptLabels blueCoord blueTrace redSupport present
      absent selected cellRealized residualLeaf residualLeafMass horder
      horder_set hp hp_half hBcard hBterm hgeom hleaf_nonneg hleaf_sum
      hleaf_inj hleaf_dom
  refine
    ⟨fun β τ =>
      if τ ∈ transcriptLabels ∧ cellRealized β τ then residualMass β τ else 0,
      ?_, ?_, ?_⟩
  · intro β τ hτ
    by_cases hreal : cellRealized β τ
    · simpa [hτ, hreal] using hres_nonneg β τ hτ hreal
    · simp [hreal]
  · have hsum_eq :
        (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              transcriptLabels.sum
                (fun τ =>
                  if τ ∈ transcriptLabels ∧ cellRealized β τ then
                    residualMass β τ
                  else
                    0))
          =
          (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => residualMass β τ)) := by
      apply Finset.sum_congr rfl
      intro β _hβ
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro τ hτ
      by_cases hreal : cellRealized β τ
      · simp [hτ, hreal]
      · simp [hreal]
    simpa [hsum_eq] using hres_sum
  · intro β τ hτ hreal
    simp [hτ, hreal]
    rcases hgeom β τ hτ hreal with
      ⟨hRcard, _hRterm, hBRdisj, _hPterm, _hAterm, hPAdisj, hBRsub,
        _hblue, hZsub, hZlarge⟩
    have hBsubP : B ⊆ present τ :=
      Finset.Subset.trans Finset.subset_union_left hBRsub
    have hRsubP : redSupport β ⊆ present τ :=
      Finset.Subset.trans Finset.subset_union_right hBRsub
    exact
      FixedSetHistoryCellRedTermwiseCylinderDomination
        B (redSupport β) (present τ) (absent τ) (selected τ)
        hp hp_half (hres_nonneg β τ hτ hreal) hBcard hRcard hBsubP
        hRsubP hBRdisj hZsub hPAdisj hZlarge
        (hres_dom β τ hτ hreal)
