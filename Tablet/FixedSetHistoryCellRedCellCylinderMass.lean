import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.TwoBiteConditionalIntersectionBound
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: FixedSetHistoryCellRedCellCylinderMass]

theorem FixedSetHistoryCellRedCellCylinderMass :
    ∀ {n m : ℕ} {p : ℝ}
      (hist target : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (blueSupportLabels :
        Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {BranchLabel : Type} [Fintype BranchLabel]
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {RedLabel : Type} [Fintype RedLabel]
      (cellEvent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          RedLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          TwoBiteSample n m p → Prop),
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
      (∀ B,
        B ∈ blueSupportLabels →
          ∀ J : RedLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  ∀ ω : TwoBiteSample n m p,
                    cellEvent B J β τ ω →
                      τ.1 ⊆ terminal ∧
                      τ.2.1 ⊆ terminal ∧
                      Disjoint τ.1 τ.2.1 ∧
                      (∀ e,
                        e ∈ τ.1 →
                          TwoBiteEdgeCoordinateValue ω e) ∧
                      (∀ e,
                        e ∈ τ.2.1 →
                          ¬ TwoBiteEdgeCoordinateValue ω e)) →
      ∃ cellWeight :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          RedLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ,
        (∀ B,
          B ∈ blueSupportLabels →
            ∀ J : RedLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    0 ≤ cellWeight B J β τ) ∧
        (∀ B,
          B ∈ blueSupportLabels →
            ∀ J : RedLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    cellWeight B J β τ
                      ≤
                      p ^ τ.1.card *
                        ((1 : ℝ) - p) ^ τ.2.1.card) ∧
        (∀ B,
          B ∈ blueSupportLabels →
            ∀ J : RedLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    TwoBiteEventProbability n m p
                        (fun ω =>
                          target ω ∧ hist ω ∧
                            cellEvent B J β τ ω)
                      ≤
                      TwoBiteEventProbability n m p hist *
                        cellWeight B J β τ) := by
-- BODY
  classical
  intro n m p hist target terminal blueSupportLabels BranchLabel _ transcriptLabels
    RedLabel _ cellEvent hp0 hphalf hproduct hcell_geometry
  have hp1 : p ≤ (1 : ℝ) := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by norm_num
    exact le_trans hphalf hhalf_le_one
  have hone_minus_nonneg : 0 ≤ (1 : ℝ) - p := sub_nonneg.mpr hp1
  let cellWeight :
      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
        RedLabel →
        BranchLabel →
        (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
        ℝ :=
    fun _ _ _ τ => p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card
  refine ⟨cellWeight, ?_, ?_, ?_⟩
  · intro B hB J β τ hτ
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hone_minus_nonneg _)
  · intro B hB J β τ hτ
    exact le_rfl
  · intro B hB J β τ hτ
    let cylinder : TwoBiteSample n m p → Prop := fun ω =>
      (∀ e, e ∈ τ.1 → TwoBiteEdgeCoordinateValue ω e) ∧
        (∀ e, e ∈ τ.2.1 → ¬ TwoBiteEdgeCoordinateValue ω e)
    let weight : ℝ := p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card
    have hweight_nonneg : 0 ≤ weight := by
      exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg hone_minus_nonneg _)
    have hsample_nonneg :
        ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
      intro ω
      exact TwoBiteSampleWeightNonnegative ω hp0 hp1
    let prob : (TwoBiteSample n m p → Prop) → ℝ :=
      fun E => TwoBiteEventProbability n m p E
    have hprob_nonneg :
        ∀ E : TwoBiteSample n m p → Prop, 0 ≤ prob E := by
      intro E
      unfold prob TwoBiteEventProbability
      exact Finset.sum_nonneg (by
        intro ω hω
        exact hsample_nonneg ω)
    have hprob_mono :
        ∀ {E F : TwoBiteSample n m p → Prop},
          (∀ ω, E ω → F ω) → prob E ≤ prob F := by
      intro E F hEF
      unfold prob TwoBiteEventProbability
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
          exact hEF ω hω)
        (by
          intro ω hωF hωnotE
          exact hsample_nonneg ω)
    by_cases hnonempty :
        ∃ ω : TwoBiteSample n m p,
          target ω ∧ hist ω ∧ cellEvent B J β τ ω
    · rcases hnonempty with ⟨ω0, htarget0, hhist0, hcell0⟩
      have hgeom0 := hcell_geometry B hB J β τ hτ ω0 hcell0
      have hcylinder_cond :
          TwoBiteConditionalProbability n m p cylinder hist ≤ weight := by
        simpa [cylinder, weight] using
          (FixedSetHistoryCellFixedCylinderCharge
            (n := n) (m := m) (p := p)
            hist terminal τ.1 τ.2.1 hp0 hp1
            hgeom0.1 hgeom0.2.1 hgeom0.2.2.1 hproduct)
      have hintersection :
          prob (fun ω => cylinder ω ∧ hist ω) ≤
            prob hist * min (1 : ℝ) weight := by
        simpa [prob] using
          (TwoBiteConditionalIntersectionBound
            (n := n) (m := m) (p := p)
            (cellBound := prob hist) (condBound := weight)
            (event := cylinder) (condition := hist)
            hsample_nonneg (hprob_nonneg hist) hweight_nonneg
            le_rfl hcylinder_cond)
      have hraw_le_cylinder :
          prob (fun ω => target ω ∧ hist ω ∧ cellEvent B J β τ ω) ≤
            prob (fun ω => cylinder ω ∧ hist ω) := by
        refine hprob_mono ?_
        intro ω hω
        have hgeom := hcell_geometry B hB J β τ hτ ω hω.2.2
        exact ⟨⟨hgeom.2.2.2.1, hgeom.2.2.2.2⟩, hω.2.1⟩
      have hmin_to_weight :
          prob hist * min (1 : ℝ) weight ≤ prob hist * weight := by
        exact mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) weight)
          (hprob_nonneg hist)
      exact le_trans hraw_le_cylinder (le_trans hintersection hmin_to_weight)
    · have hraw_zero :
          prob (fun ω => target ω ∧ hist ω ∧ cellEvent B J β τ ω) = 0 := by
        unfold prob TwoBiteEventProbability
        simp [not_exists.mp hnonempty]
      have hright_nonneg : 0 ≤ prob hist * weight :=
        mul_nonneg (hprob_nonneg hist) hweight_nonneg
      simpa [prob, cellWeight, weight, hraw_zero] using hright_nonneg
