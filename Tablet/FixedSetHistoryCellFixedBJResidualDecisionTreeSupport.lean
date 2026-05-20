import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedReleasedCylinderPacking
import Tablet.FixedSetHistoryCellSelectedAbsencePowSplit
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellFixedBJResidualDecisionTreeSupport]

theorem FixedSetHistoryCellFixedBJResidualDecisionTreeSupport :
    ∀ {n m uR uB : ℕ} {p a : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
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
      (assignmentMass :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → ℝ)
      (releasedAssignments :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      (releasedCylinderMass :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ),
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      order.Nodup →
      order.toFinset = terminal →
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
            max 0 (a - (uR : ℝ) - (uB : ℝ))
              ≤ ((τ.2.2).card : ℝ)) →
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
                τ.1 ⊆ A ∧
                Disjoint (τ.2.1 \ τ.2.2) A ∧
                ∀ e,
                  e ∈ terminal →
                    e ∉ τ.2.2 →
                      (match e with
                      | Sum.inl _ => False
                      | Sum.inr _ => True) →
                        (e ∈ blueTrace β ↔ e ∈ A)) →
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
      (∀ A,
        A ∈ terminal.powerset →
          0 ≤ assignmentMass A) →
      terminal.powerset.sum assignmentMass ≤ 1 →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedAssignments β τ ⊆ terminal.powerset) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedCylinderMass β τ =
              (releasedAssignments β τ).sum assignmentMass) →
      (∀ (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          τ' ∈ transcriptLabels →
            cellRealized β τ →
              cellRealized β' τ' →
                (β ≠ β' ∨ τ ≠ τ') →
                  A ∈ releasedAssignments β τ →
                    A ∉ releasedAssignments β' τ') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ (τ.1.card - uR - uB) *
                ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
              ≤ releasedCylinderMass β τ) →
      ∃ (ResidualLeaf : Type),
        ∃ _ : Fintype ResidualLeaf,
          ∃ _ : DecidableEq ResidualLeaf,
            ∃ residualLeaf :
              BranchLabel →
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                ResidualLeaf,
              ∃ residualLeafMass : ResidualLeaf → ℝ,
                (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) ∧
                (Finset.univ : Finset ResidualLeaf).sum residualLeafMass ≤ 1 ∧
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
                            β = β' ∧ τ = τ') ∧
                ∀ (β : BranchLabel)
                  (τ :
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
                  τ ∈ transcriptLabels →
                    cellRealized β τ →
                      p ^ (τ.1.card - uR - uB) *
                          ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
                        ≤ residualLeafMass (residualLeaf β τ) := by
-- BODY
  classical
  intro n m uR uB p a hist terminal order B BranchLabel _ blueTrace
    transcriptLabels RedLabel _ J redSupport cellRealized
    assignmentCompatible assignmentMass releasedAssignments
    releasedCylinderMass hp_nonneg hp_half horder_nodup horder_terminal
    hproduct_law hBcard hBterm hBblue hblueTrace_functional
    hrealized_geometry hcompat_forward hcompat_inj hassignment_nonneg
    hassignment_sum hreleased_subset hreleased_mass hreleased_disjoint
    hreleased_dom
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let residualLeaf : BranchLabel → Transcript → BranchLabel × Transcript :=
    fun β τ => (β, τ)
  let residualLeafMass : BranchLabel × Transcript → ℝ :=
    fun leaf =>
      if leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2 then
        releasedCylinderMass leaf.1 leaf.2
      else
        0
  have hreleased_nonneg :
      ∀ (β : BranchLabel) (τ : Transcript),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            0 ≤ releasedCylinderMass β τ := by
    intro β τ hτ hreal
    rw [hreleased_mass β τ hτ hreal]
    exact Finset.sum_nonneg (by
      intro A hA
      exact hassignment_nonneg A (hreleased_subset β τ hτ hreal hA))
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
      hassignment_nonneg hassignment_sum hreleased_subset hreleased_mass
      hreleased_disjoint
  have hleaf_sum :
      (Finset.univ : Finset (BranchLabel × Transcript)).sum residualLeafMass
        ≤ 1 := by
    have hsum_eq :
        (Finset.univ : Finset (BranchLabel × Transcript)).sum residualLeafMass
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
      ∀ (β β' : BranchLabel) (τ τ' : Transcript),
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
      ∀ (β : BranchLabel) (τ : Transcript),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            p ^ (τ.1.card - uR - uB) *
                ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
              ≤ residualLeafMass (residualLeaf β τ) := by
    intro β τ hτ hreal
    simpa [residualLeaf, residualLeafMass, hτ, hreal] using
      hreleased_dom β τ hτ hreal
  refine
    ⟨BranchLabel × Transcript, inferInstance, Classical.typeDecidableEq _,
      residualLeaf, residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj,
      hleaf_dom⟩
