import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRealizedPairBranchTranscriptSum]

theorem FixedSetHistoryCellRealizedPairBranchTranscriptSum :
    ∀ {BranchLabel Transcript : Type} [Fintype BranchLabel]
      (transcriptLabels : Finset Transcript)
      (M : ℝ)
      (cellWeight residualMass : BranchLabel → Transcript → ℝ)
      (cellRealized : BranchLabel → Transcript → Prop)
      [∀ β : BranchLabel, DecidablePred (fun τ => cellRealized β τ)],
      0 ≤ M →
      (∀ β τ, τ ∈ transcriptLabels → ¬ cellRealized β τ →
        cellWeight β τ = 0) →
      (∀ β τ, τ ∈ transcriptLabels → cellRealized β τ →
        cellWeight β τ ≤ M * residualMass β τ) →
      (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => M * residualMass β τ))
        ≤ M →
      (Finset.univ : Finset BranchLabel).sum
          (fun β => transcriptLabels.sum (fun τ => cellWeight β τ))
        ≤ M := by
-- BODY
  classical
  intro BranchLabel Transcript _ transcriptLabels M cellWeight residualMass
    cellRealized _ hM hzero hdom hmass
  have hsum_eq :
      (Finset.univ : Finset BranchLabel).sum
          (fun β => transcriptLabels.sum (fun τ => cellWeight β τ))
        =
        (Finset.univ : Finset BranchLabel).sum
          (fun β =>
            (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
              (fun τ => cellWeight β τ)) := by
    apply Finset.sum_congr rfl
    intro β _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases hreal : cellRealized β τ
    · simp [hreal]
    · simp [hreal, hzero β τ hτ hreal]
  calc
    (Finset.univ : Finset BranchLabel).sum
        (fun β => transcriptLabels.sum (fun τ => cellWeight β τ))
      =
      (Finset.univ : Finset BranchLabel).sum
        (fun β =>
          (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
            (fun τ => cellWeight β τ)) := hsum_eq
    _ ≤
      (Finset.univ : Finset BranchLabel).sum
        (fun β =>
          (transcriptLabels.filter (fun τ => cellRealized β τ)).sum
            (fun τ => M * residualMass β τ)) := by
        apply Finset.sum_le_sum
        intro β _
        apply Finset.sum_le_sum
        intro τ hτ
        exact hdom β τ (Finset.mem_filter.mp hτ).1
          (Finset.mem_filter.mp hτ).2
    _ ≤ M := hmass
