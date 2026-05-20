import Mathlib.Tactic.Linarith
import Tablet.FinsetPowersetCylinderMass
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellSelectedAbsencePowSplit

open Classical

-- [TABLET NODE: FixedSetHistoryCellRedResidualCylinderBlockMassLower]

theorem FixedSetHistoryCellRedResidualCylinderBlockMassLower :
    ∀ {Coord BranchLabel Transcript : Type} [DecidableEq Coord]
      {uR uB : ℕ} {p : ℝ}
      (terminal B R present absent selected : Finset Coord)
      (β : BranchLabel) (τ : Transcript)
      (branchOfAssignment : Finset Coord → BranchLabel)
      (scanTranscript : Finset Coord → Option Transcript)
      (releasedBlock : Finset (Finset Coord))
      (assignmentMass : Finset Coord → ℝ)
      (blockMass : ℝ),
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      B.card = uB →
      R.card = uR →
      B ⊆ terminal →
      R ⊆ terminal →
      present ⊆ terminal →
      absent ⊆ terminal →
      selected ⊆ absent →
      Disjoint present absent →
      B ∪ R ⊆ present →
      Disjoint B R →
      releasedBlock ⊆ terminal.powerset →
      (∀ A,
        A ∈ terminal.powerset →
          (present \ (B ∪ R)) ⊆ A →
            Disjoint (absent \ selected) A →
              branchOfAssignment A = β ∧ scanTranscript A = some τ) →
      (∀ A,
        A ∈ terminal.powerset →
          branchOfAssignment A = β →
            scanTranscript A = some τ →
              A ∈ releasedBlock) →
      (∀ A,
        A ∈ terminal.powerset →
          assignmentMass A =
            p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      blockMass = releasedBlock.sum assignmentMass →
      p ^ (present.card - uR - uB) *
          ((1 : ℝ) - p) ^ (absent.card - selected.card) ≤ blockMass := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ uR uB p terminal B R present absent
    selected β τ branchOfAssignment scanTranscript releasedBlock
    assignmentMass blockMass hp hp_half hBcard hRcard _hBterm _hRterm
    hpresent_terminal habsent_terminal hselected_absent hpresent_absent
    hfixed_present hBRdisj hreleased_subset hscan_stable hblock_complete
    hmass hblockMass
  let residualPresent : Finset Coord := present \ (B ∪ R)
  let residualAbsent : Finset Coord := absent \ selected
  let cylinder : Finset (Finset Coord) :=
    terminal.powerset.filter
      (fun A => residualPresent ⊆ A ∧ Disjoint residualAbsent A)
  have hp_one : p ≤ (1 : ℝ) := by
    linarith
  have hq_nonneg : 0 ≤ (1 : ℝ) - p := by
    linarith
  have hresidualPresent_terminal : residualPresent ⊆ terminal := by
    intro e he
    exact hpresent_terminal (Finset.mem_sdiff.mp he).1
  have hresidualAbsent_terminal : residualAbsent ⊆ terminal := by
    intro e he
    exact habsent_terminal (Finset.mem_sdiff.mp he).1
  have hresidual_disjoint :
      Disjoint residualPresent residualAbsent := by
    exact
      (hpresent_absent.mono_left Finset.sdiff_subset).mono_right
        Finset.sdiff_subset
  have hcylinder_subset : cylinder ⊆ releasedBlock := by
    intro A hA
    rcases Finset.mem_filter.mp hA with ⟨hApow, hpresent_res, habsent_res⟩
    rcases hscan_stable A hApow hpresent_res habsent_res with
      ⟨hbranch, hscan⟩
    exact hblock_complete A hApow hbranch hscan
  have hcylinder_sum_product :
      cylinder.sum
          (fun A =>
            p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
        =
        p ^ residualPresent.card *
          ((1 : ℝ) - p) ^ residualAbsent.card := by
    simpa [cylinder, residualPresent, residualAbsent] using
      FinsetPowersetCylinderMass terminal residualPresent residualAbsent p
        hresidualPresent_terminal hresidualAbsent_terminal
        hresidual_disjoint
  have hcylinder_sum_mass :
      cylinder.sum assignmentMass =
        p ^ residualPresent.card *
          ((1 : ℝ) - p) ^ residualAbsent.card := by
    calc
      cylinder.sum assignmentMass =
          cylinder.sum
            (fun A =>
              p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
          apply Finset.sum_congr rfl
          intro A hA
          exact hmass A (Finset.mem_filter.mp hA).1
      _ =
          p ^ residualPresent.card *
            ((1 : ℝ) - p) ^ residualAbsent.card :=
          hcylinder_sum_product
  have hcylinder_sum_le_block :
      cylinder.sum assignmentMass ≤ releasedBlock.sum assignmentMass := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hcylinder_subset ?_
    intro A hAblock _hAnot
    have hApow : A ∈ terminal.powerset := hreleased_subset hAblock
    rw [hmass A hApow]
    exact mul_nonneg (pow_nonneg hp _) (pow_nonneg hq_nonneg _)
  have hfixed_card : (B ∪ R).card = uB + uR := by
    rw [Finset.card_union_of_disjoint hBRdisj, hBcard, hRcard]
  have hresidualPresent_card :
      residualPresent.card = present.card - uR - uB := by
    have hsdiff := Finset.card_sdiff_of_subset hfixed_present
    calc
      residualPresent.card = present.card - (B ∪ R).card := by
        simpa [residualPresent] using hsdiff
      _ = present.card - (uR + uB) := by
        rw [hfixed_card, Nat.add_comm]
      _ = present.card - uR - uB := by
        rw [Nat.sub_sub]
  have hresidualAbsent_card :
      residualAbsent.card = absent.card - selected.card := by
    simpa [residualAbsent] using
      Finset.card_sdiff_of_subset hselected_absent
  calc
    p ^ (present.card - uR - uB) *
        ((1 : ℝ) - p) ^ (absent.card - selected.card)
        =
        p ^ residualPresent.card *
          ((1 : ℝ) - p) ^ residualAbsent.card := by
          rw [hresidualPresent_card, hresidualAbsent_card]
    _ = cylinder.sum assignmentMass := hcylinder_sum_mass.symm
    _ ≤ releasedBlock.sum assignmentMass := hcylinder_sum_le_block
    _ = blockMass := hblockMass.symm
