import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedTwoStageResidualCertificate]

theorem FixedSetHistoryCellRedTwoStageResidualCertificate :
    ∀ {Cell Leaf : Type} [Fintype Cell] [Fintype Leaf] [DecidableEq Leaf]
      (cellWeight : Cell → ℝ)
      (leafOf : Cell → Leaf)
      (leafMass : Leaf → ℝ)
      {M : ℝ},
      0 ≤ M →
      (∀ leaf : Leaf, 0 ≤ leafMass leaf) →
      (Finset.univ.sum leafMass ≤ 1) →
      Function.Injective leafOf →
      (∀ c : Cell, cellWeight c ≤ M * leafMass (leafOf c)) →
      ∃ residualMass : Cell → ℝ,
        Finset.univ.sum (fun c : Cell => M * residualMass c) ≤ M ∧
          ∀ c : Cell, cellWeight c ≤ M * residualMass c := by
-- BODY
  intro Cell Leaf _ _ _ cellWeight leafOf leafMass M hM hleaf_nonneg
    hleaf_sum hleaf_inj hdom
  refine ⟨fun c => leafMass (leafOf c), ?_, hdom⟩
  have hsum_image :
      (Finset.univ : Finset Cell).sum (fun c => M * leafMass (leafOf c))
        = ((Finset.univ : Finset Cell).image leafOf).sum
            (fun leaf => M * leafMass leaf) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hleaf_inj hab
  have hsubset :
      (Finset.univ : Finset Cell).image leafOf ⊆
        (Finset.univ : Finset Leaf) := by
    intro x _
    exact Finset.mem_univ x
  have hnonneg_extra :
      ∀ x ∈ (Finset.univ : Finset Leaf),
        x ∉ (Finset.univ : Finset Cell).image leafOf →
          0 ≤ M * leafMass x := by
    intro x _ _
    exact mul_nonneg hM (hleaf_nonneg x)
  have hsum_subset :
      ((Finset.univ : Finset Cell).image leafOf).sum
          (fun leaf => M * leafMass leaf)
        ≤ (Finset.univ : Finset Leaf).sum
          (fun leaf => M * leafMass leaf) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg_extra
  have hmul_sum :
      (Finset.univ : Finset Leaf).sum (fun leaf => M * leafMass leaf)
        = M * (Finset.univ : Finset Leaf).sum leafMass := by
    simp [Finset.mul_sum]
  have hmul_le : M * (Finset.univ : Finset Leaf).sum leafMass ≤ M * 1 := by
    exact mul_le_mul_of_nonneg_left hleaf_sum hM
  have hone : M * 1 = M := by ring
  calc
    (Finset.univ : Finset Cell).sum (fun c => M * leafMass (leafOf c))
        = ((Finset.univ : Finset Cell).image leafOf).sum
            (fun leaf => M * leafMass leaf) := hsum_image
    _ ≤ (Finset.univ : Finset Leaf).sum
          (fun leaf => M * leafMass leaf) := hsum_subset
    _ = M * (Finset.univ : Finset Leaf).sum leafMass := hmul_sum
    _ ≤ M * 1 := hmul_le
    _ = M := hone
