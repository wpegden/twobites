import Tablet.FixedSetHistoryCellRedReleasedCylinderPacking

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualLeafCertificate]

theorem FixedSetHistoryCellFixedBJResidualLeafCertificate :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord] [DecidableEq BranchLabel] [DecidableEq Transcript]
      [Fintype BranchLabel] [Fintype Transcript]
      {uR uB : ℕ} {p : ℝ}
      (terminal : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (present absent selected : Transcript → Finset Coord)
      (cellRealized : BranchLabel → Transcript → Prop)
      [∀ β : BranchLabel, DecidablePred (fun τ => cellRealized β τ)]
      (assignmentMass : Finset Coord → ℝ)
      (releasedAssignments : BranchLabel → Transcript → Finset (Finset Coord))
      (releasedCylinderMass : BranchLabel → Transcript → ℝ),
      (∀ A, A ∈ terminal.powerset → 0 ≤ assignmentMass A) →
      terminal.powerset.sum assignmentMass ≤ 1 →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedAssignments β τ ⊆ terminal.powerset) →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedCylinderMass β τ =
              (releasedAssignments β τ).sum assignmentMass) →
      (∀ β β' τ τ' A,
        τ ∈ transcriptLabels →
          τ' ∈ transcriptLabels →
            cellRealized β τ →
              cellRealized β' τ' →
                (β ≠ β' ∨ τ ≠ τ') →
                  A ∈ releasedAssignments β τ →
                    A ∉ releasedAssignments β' τ') →
      (∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ ((present τ).card - uR - uB) *
                ((1 : ℝ) - p) ^
                  ((absent τ).card - (selected τ).card)
              ≤ releasedCylinderMass β τ) →
      ∃ (ResidualLeaf : Type),
        ∃ _ : Fintype ResidualLeaf,
          ∃ _ : DecidableEq ResidualLeaf,
            ∃ residualLeaf : BranchLabel → Transcript → ResidualLeaf,
              ∃ residualLeafMass : ResidualLeaf → ℝ,
                (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) ∧
                (Finset.univ : Finset ResidualLeaf).sum residualLeafMass ≤ 1 ∧
                (∀ (β β' : BranchLabel) (τ τ' : Transcript),
                  τ ∈ transcriptLabels →
                    τ' ∈ transcriptLabels →
                      cellRealized β τ →
                        cellRealized β' τ' →
                          residualLeaf β τ = residualLeaf β' τ' →
                            β = β' ∧ τ = τ') ∧
                ∀ β τ,
                  τ ∈ transcriptLabels →
                    cellRealized β τ →
                      p ^ ((present τ).card - uR - uB) *
                          ((1 : ℝ) - p) ^
                            ((absent τ).card - (selected τ).card)
                        ≤ residualLeafMass (residualLeaf β τ) := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ _ _ uR uB p terminal
    transcriptLabels present absent selected cellRealized _
    assignmentMass releasedAssignments releasedCylinderMass hmass_nonneg
    hmass_sum hreleased_subset hreleased_mass hreleased_disjoint
    hreleased_dom
  let residualLeaf : BranchLabel → Transcript → BranchLabel × Transcript :=
    fun β τ => (β, τ)
  let residualLeafMass : BranchLabel × Transcript → ℝ :=
    fun leaf =>
      if leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 then
        releasedCylinderMass leaf.1 leaf.2
      else
        0
  have hreleased_nonneg :
      ∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            0 ≤ releasedCylinderMass β τ := by
    intro β τ hτ hreal
    rw [hreleased_mass β τ hτ hreal]
    exact Finset.sum_nonneg (by
      intro A hA
      exact hmass_nonneg A (hreleased_subset β τ hτ hreal hA))
  have hleaf_nonneg :
      ∀ leaf : BranchLabel × Transcript, 0 ≤ residualLeafMass leaf := by
    intro leaf
    by_cases hreal : leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2
    · simpa [residualLeafMass, hreal] using
        hreleased_nonneg leaf.1 leaf.2 hreal.1 hreal.2
    · simp [residualLeafMass, hreal]
  have hreleased_sum :
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => releasedCylinderMass β τ))
        ≤ 1 :=
    FixedSetHistoryCellRedReleasedCylinderPacking
      (terminal := terminal) (transcriptLabels := transcriptLabels)
      (cellRealized := cellRealized) (assignmentMass := assignmentMass)
      (releasedAssignments := releasedAssignments)
      (releasedCylinderMass := releasedCylinderMass)
      hmass_nonneg hmass_sum hreleased_subset hreleased_mass
      hreleased_disjoint
  have hleaf_sum :
      (Finset.univ : Finset (BranchLabel × Transcript)).sum residualLeafMass
        ≤ 1 := by
    have hsum_eq :
        (Finset.univ : Finset (BranchLabel × Transcript)).sum
            residualLeafMass
          =
          (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
                (fun τ => releasedCylinderMass β τ)) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro β _hβ
      have hfilter :
          (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => releasedCylinderMass β τ)
            =
            (Finset.univ : Finset Transcript).sum
              (fun τ =>
                if τ ∈ transcriptLabels ∧ cellRealized β τ then
                  releasedCylinderMass β τ
                else
                  0) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext τ
          simp
        · intro τ _hτ
          rfl
      simpa [residualLeafMass] using hfilter.symm
    rw [hsum_eq]
    exact hreleased_sum
  have hleaf_inj :
      ∀ β β' τ τ',
        τ ∈ transcriptLabels →
          τ' ∈ transcriptLabels →
            cellRealized β τ →
              cellRealized β' τ' →
                residualLeaf β τ = residualLeaf β' τ' →
                  β = β' ∧ τ = τ' := by
    intro β β' τ τ' _hτ _hτ' _hreal _hreal' hleaf
    injection hleaf with hβ hτeq
    exact ⟨hβ, hτeq⟩
  have hleaf_dom :
      ∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ ((present τ).card - uR - uB) *
                ((1 : ℝ) - p) ^
                  ((absent τ).card - (selected τ).card)
              ≤ residualLeafMass (residualLeaf β τ) := by
    intro β τ hτ hreal
    simpa [residualLeaf, residualLeafMass, hτ, hreal] using
      hreleased_dom β τ hτ hreal
  exact
    ⟨BranchLabel × Transcript, inferInstance, inferInstance, residualLeaf,
      residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj, hleaf_dom⟩
