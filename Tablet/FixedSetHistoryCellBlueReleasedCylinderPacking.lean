import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellBlueReleasedCylinderPacking]

theorem FixedSetHistoryCellBlueReleasedCylinderPacking :
    ∀ {Coord BranchLabel Transcript : Type}
      [DecidableEq Coord]
      [Fintype BranchLabel] [DecidableEq BranchLabel]
      [Fintype Transcript] [DecidableEq Transcript]
      (terminal : Finset Coord)
      (transcriptLabels : Finset Transcript)
      (cellRealized : BranchLabel → Transcript → Prop)
      [∀ β : BranchLabel, DecidablePred (fun τ => cellRealized β τ)]
      (assignmentMass : Finset Coord → ℝ)
      (releasedAssignments :
        BranchLabel → Transcript → Finset (Finset Coord))
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
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => releasedCylinderMass β τ))
        ≤ 1 := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ _ _ _ _ terminal transcriptLabels
    cellRealized _ assignmentMass releasedAssignments releasedCylinderMass
    hmass_nonneg htotal_mass hreleased_subset hreleased_mass
    hreleased_disjoint
  let cells : Finset (BranchLabel × Transcript) :=
    ((Finset.univ : Finset BranchLabel).product transcriptLabels).filter
      (fun c => cellRealized c.1 c.2)
  have hsum_cells :
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => releasedCylinderMass β τ))
        =
        cells.sum (fun c => releasedCylinderMass c.1 c.2) := by
    simp [cells, Finset.sum_product, Finset.sum_filter]
  have hsum_released :
      cells.sum (fun c => releasedCylinderMass c.1 c.2)
        =
        cells.sum
          (fun c => (releasedAssignments c.1 c.2).sum assignmentMass) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hc_prod :
        c ∈ (Finset.univ : Finset BranchLabel).product transcriptLabels :=
      (Finset.mem_filter.mp hc).1
    have hc_transcript : c.2 ∈ transcriptLabels :=
      (Finset.mem_product.mp hc_prod).2
    have hc_realized : cellRealized c.1 c.2 :=
      (Finset.mem_filter.mp hc).2
    exact hreleased_mass c.1 c.2 hc_transcript hc_realized
  have hpairwise :
      (↑cells : Set (BranchLabel × Transcript)).PairwiseDisjoint
        (fun c => releasedAssignments c.1 c.2) := by
    rw [Finset.pairwiseDisjoint_iff]
    intro c hc d hd hnonempty
    by_contra hne
    rcases hnonempty with ⟨A, hA⟩
    have hA_left : A ∈ releasedAssignments c.1 c.2 :=
      (Finset.mem_inter.mp hA).1
    have hA_right : A ∈ releasedAssignments d.1 d.2 :=
      (Finset.mem_inter.mp hA).2
    have hc_prod :
        c ∈ (Finset.univ : Finset BranchLabel).product transcriptLabels :=
      (Finset.mem_filter.mp hc).1
    have hd_prod :
        d ∈ (Finset.univ : Finset BranchLabel).product transcriptLabels :=
      (Finset.mem_filter.mp hd).1
    have hc_transcript : c.2 ∈ transcriptLabels :=
      (Finset.mem_product.mp hc_prod).2
    have hd_transcript : d.2 ∈ transcriptLabels :=
      (Finset.mem_product.mp hd_prod).2
    have hc_realized : cellRealized c.1 c.2 :=
      (Finset.mem_filter.mp hc).2
    have hd_realized : cellRealized d.1 d.2 :=
      (Finset.mem_filter.mp hd).2
    have hdifferent : c.1 ≠ d.1 ∨ c.2 ≠ d.2 := by
      by_cases hβ : c.1 = d.1
      · right
        intro hτ
        apply hne
        cases c
        cases d
        simp_all
      · exact Or.inl hβ
    exact
      (hreleased_disjoint c.1 d.1 c.2 d.2 A hc_transcript
        hd_transcript hc_realized hd_realized hdifferent hA_left) hA_right
  have hsum_union :
      (cells.biUnion (fun c => releasedAssignments c.1 c.2)).sum
          assignmentMass
        =
        cells.sum
          (fun c => (releasedAssignments c.1 c.2).sum assignmentMass) := by
    exact Finset.sum_biUnion hpairwise
  have hunion_subset :
      cells.biUnion (fun c => releasedAssignments c.1 c.2)
        ⊆ terminal.powerset := by
    intro A hA
    rw [Finset.mem_biUnion] at hA
    rcases hA with ⟨c, hc, hA_mem⟩
    have hc_prod :
        c ∈ (Finset.univ : Finset BranchLabel).product transcriptLabels :=
      (Finset.mem_filter.mp hc).1
    have hc_transcript : c.2 ∈ transcriptLabels :=
      (Finset.mem_product.mp hc_prod).2
    have hc_realized : cellRealized c.1 c.2 :=
      (Finset.mem_filter.mp hc).2
    exact hreleased_subset c.1 c.2 hc_transcript hc_realized hA_mem
  have hsum_le_total :
      (cells.biUnion (fun c => releasedAssignments c.1 c.2)).sum
          assignmentMass
        ≤ terminal.powerset.sum assignmentMass :=
    Finset.sum_le_sum_of_subset_of_nonneg hunion_subset
      (by
        intro A hA _hA_not_in_union
        exact hmass_nonneg A hA)
  calc
    (Finset.univ : Finset BranchLabel).sum
        (fun β =>
          (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
            (fun τ => releasedCylinderMass β τ))
        =
        cells.sum (fun c => releasedCylinderMass c.1 c.2) := hsum_cells
    _ =
        cells.sum
          (fun c => (releasedAssignments c.1 c.2).sum assignmentMass) :=
        hsum_released
    _ =
        (cells.biUnion (fun c => releasedAssignments c.1 c.2)).sum
          assignmentMass := hsum_union.symm
    _ ≤ terminal.powerset.sum assignmentMass := hsum_le_total
    _ ≤ 1 := htotal_mass
