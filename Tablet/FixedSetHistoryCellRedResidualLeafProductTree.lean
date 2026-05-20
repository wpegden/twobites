import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.Preamble
import Tablet.FixedSetHistoryCellRedTermwiseCylinderDomination

-- [TABLET NODE: FixedSetHistoryCellRedResidualLeafProductTree]

theorem FixedSetHistoryCellRedResidualLeafProductTree :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord]
      [Fintype BranchLabel] [DecidableEq BranchLabel]
      [Fintype Transcript] [DecidableEq Transcript]
      (p a : ℝ) (uR uB : ℕ)
      (terminal B : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (redSupport : BranchLabel → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      [∀ β : BranchLabel, DecidablePred (fun τ => cellRealized β τ)]
      (releasedCylinderMass : BranchLabel → Transcript → ℝ),
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
            selected τ ⊆ absent τ ∧
            max 0 (a - (uR : ℝ) - (uB : ℝ))
              ≤ ((selected τ).card : ℝ)) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            0 ≤ releasedCylinderMass β τ) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedCylinderMass β τ =
              p ^ ((present τ).card - uR - uB) *
                ((1 : ℝ) - p) ^ ((absent τ).card - (selected τ).card)) →
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => releasedCylinderMass β τ))
        ≤ 1 →
      ∃ (ResidualLeaf : Type),
        ∃ _ : Fintype ResidualLeaf,
          ∃ _ : DecidableEq ResidualLeaf,
            ∃ residualLeaf : BranchLabel → Transcript → ResidualLeaf,
              ∃ residualLeafMass : ResidualLeaf → ℝ,
                (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) ∧
                (Finset.univ : Finset ResidualLeaf).sum residualLeafMass ≤ 1 ∧
                (∀ β β' : BranchLabel,
                  ∀ τ τ',
                    τ ∈ transcriptLabels →
                      τ' ∈ transcriptLabels →
                        cellRealized β τ →
                          cellRealized β' τ' →
                            residualLeaf β τ = residualLeaf β' τ' →
                              β = β' ∧ τ = τ') ∧
                ∀ β : BranchLabel,
                  ∀ τ,
                    τ ∈ transcriptLabels →
                      cellRealized β τ →
                        p ^ (present τ).card *
                            ((1 : ℝ) - p) ^ (absent τ).card
                          ≤
                          p ^ uR * p ^ uB *
                              Real.rpow ((1 : ℝ) - p)
                                (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
                            residualLeafMass (residualLeaf β τ) := by
-- BODY
  intros Coord BranchLabel Transcript _ _ _ _ _ p a uR uB terminal B transcriptLabels present absent selected redSupport cellRealized _ releasedCylinderMass hp hp_half h_B_card h_B_term h_props h_mass_nonneg h_mass_eq h_sum_le_one
  refine ⟨BranchLabel × Transcript, inferInstance, inferInstance, fun β τ => (β, τ), fun leaf => if leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 then releasedCylinderMass leaf.1 leaf.2 else 0, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro leaf
    dsimp only
    split_ifs with h
    · exact h_mass_nonneg leaf.1 leaf.2 h.1 h.2
    · rfl
  · dsimp only
    have h_rw : (Finset.univ : Finset (BranchLabel × Transcript)).sum (fun leaf => if leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 then releasedCylinderMass leaf.1 leaf.2 else 0) =
                (Finset.univ : Finset BranchLabel).sum (fun β => (transcriptLabels.filter (fun τ => cellRealized β τ)).sum (fun τ => releasedCylinderMass β τ)) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro β _
      have h_sum_filter : (transcriptLabels.filter (fun τ => cellRealized β τ)).sum (fun τ => releasedCylinderMass β τ) =
        (Finset.univ : Finset Transcript).sum (fun τ => if τ ∈ transcriptLabels ∧ cellRealized β τ then releasedCylinderMass β τ else 0) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext x; simp
        · intro _ _; rfl
      exact h_sum_filter.symm
    rw [h_rw]
    exact h_sum_le_one
  · intro β β' τ τ' _ _ _ _ heq
    injection heq with h1 h2
    exact ⟨h1, h2⟩
  · intro β τ hτ hreal
    dsimp only
    have h1 : (if τ ∈ transcriptLabels ∧ cellRealized β τ then releasedCylinderMass β τ else 0) = releasedCylinderMass β τ := by
      rw [if_pos ⟨hτ, hreal⟩]
    rw [h1]
    have props := h_props β τ hτ hreal
    have h_mass := h_mass_eq β τ hτ hreal
    exact FixedSetHistoryCellRedTermwiseCylinderDomination B (redSupport β) (present τ) (absent τ) (selected τ) hp hp_half (h_mass_nonneg β τ hτ hreal) h_B_card props.1 (Finset.Subset.trans Finset.subset_union_left props.2.2.2.2.2.2.1) (Finset.Subset.trans Finset.subset_union_right props.2.2.2.2.2.2.1) props.2.2.1 props.2.2.2.2.2.2.2.1 props.2.2.2.2.2.1 props.2.2.2.2.2.2.2.2 (by rw [h_mass])
