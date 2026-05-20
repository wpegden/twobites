import Tablet.FixedSetHistoryCellTerminalAssignmentExtension

open Classical

-- [TABLET NODE: FixedSetHistoryCellRISIResidualScanStability]

theorem FixedSetHistoryCellRISIResidualScanStability :
    ∀ {Coord BranchLabel Transcript : Type} [DecidableEq Coord]
      (terminal : Finset Coord)
      (order : List Coord)
      (present absent selected fixedSupport : Transcript → Finset Coord)
      (dependencySet : Transcript → Coord → Finset Coord)
      (stagedOpen touched sameColorClosed preTerminalRecorded :
        Finset Coord → Coord → Prop)
      (branchOfAssignment : Finset Coord → BranchLabel)
      (scanTranscript : Finset Coord → Option Transcript)
      (witness residualAssignment : Finset Coord)
      (β : BranchLabel) (τ : Transcript),
      order.toFinset = terminal →
      present τ ⊆ terminal →
      absent τ ⊆ terminal →
      witness ⊆ terminal →
      residualAssignment ⊆ terminal →
      fixedSupport τ ⊆ present τ →
      selected τ ⊆ absent τ →
      Disjoint (present τ) (absent τ) →
      (∀ e, e ∈ present τ → e ∈ witness) →
      (∀ e, e ∈ absent τ → e ∉ witness) →
      (present τ \ fixedSupport τ) ⊆ residualAssignment →
      Disjoint (absent τ \ selected τ) residualAssignment →
      (∀ e,
        e ∈ terminal →
          dependencySet τ e ⊆ present τ ∪ absent τ) →
      (∀ A,
        A ⊆ terminal →
          ∀ e,
            e ∈ terminal →
              (∀ c,
                c ∈ dependencySet τ e →
                  (c ∈ witness ↔ c ∈ A)) →
            (stagedOpen witness e ↔
              stagedOpen A e) ∧
            (touched witness e ↔ touched A e) ∧
            (sameColorClosed witness e ↔ sameColorClosed A e) ∧
            (preTerminalRecorded witness e ↔
              preTerminalRecorded A e)) →
      (∀ A,
        A ⊆ terminal →
        (∀ e,
          e ∈ terminal →
            (stagedOpen witness e ↔ stagedOpen A e) ∧
            (touched witness e ↔ touched A e) ∧
            (sameColorClosed witness e ↔ sameColorClosed A e) ∧
            (preTerminalRecorded witness e ↔ preTerminalRecorded A e)) →
          branchOfAssignment A = β ∧ scanTranscript A = some τ) →
      (∀ e,
        e ∈ terminal →
          ∀ c,
            c ∈ dependencySet τ e →
              (c ∈ witness ↔
                c ∈ ((residualAssignment \ selected τ) ∪ fixedSupport τ))) ∧
      ((residualAssignment \ selected τ) ∪ fixedSupport τ) ⊆ terminal ∧
      (∀ e,
        e ∈ terminal →
          (stagedOpen witness e ↔
            stagedOpen
              ((residualAssignment \ selected τ) ∪ fixedSupport τ) e) ∧
          (touched witness e ↔
            touched
              ((residualAssignment \ selected τ) ∪ fixedSupport τ) e) ∧
          (sameColorClosed witness e ↔
            sameColorClosed
              ((residualAssignment \ selected τ) ∪ fixedSupport τ) e) ∧
          (preTerminalRecorded witness e ↔
            preTerminalRecorded
              ((residualAssignment \ selected τ) ∪ fixedSupport τ) e)) ∧
      branchOfAssignment ((residualAssignment \ selected τ) ∪ fixedSupport τ)
          = β ∧
        scanTranscript ((residualAssignment \ selected τ) ∪ fixedSupport τ)
          = some τ := by
-- BODY
  classical
  intro Coord BranchLabel Transcript _ terminal order present absent selected
    fixedSupport dependencySet stagedOpen touched sameColorClosed
    preTerminalRecorded branchOfAssignment scanTranscript witness
    residualAssignment β τ _horder hpresent_terminal habsent_terminal
    _hwitness_terminal hresidual_terminal hfixed_present hselected_absent
    hpresent_absent hwitness_present hwitness_absent hpresent_residual
    habsent_residual hdependency_coverage hprefix_safety hscan_deterministic
  let reconstructed : Finset Coord :=
    (residualAssignment \ selected τ) ∪ fixedSupport τ
  have hreconstructed_terminal : reconstructed ⊆ terminal := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc_residual | hc_fixed
    · exact hresidual_terminal (Finset.mem_sdiff.mp hc_residual).1
    · exact hpresent_terminal (hfixed_present hc_fixed)
  have hdependency_agreement :
      ∀ e,
        e ∈ terminal →
          ∀ c,
            c ∈ dependencySet τ e →
              (c ∈ witness ↔ c ∈ reconstructed) := by
    intro e he c hc
    have hcovered : c ∈ present τ ∪ absent τ :=
      hdependency_coverage e he hc
    rcases Finset.mem_union.mp hcovered with hc_present | hc_absent
    · have hcw : c ∈ witness := hwitness_present c hc_present
      have hcr : c ∈ reconstructed := by
        by_cases hc_fixed : c ∈ fixedSupport τ
        · exact Finset.mem_union.mpr (Or.inr hc_fixed)
        · have hc_residual : c ∈ residualAssignment :=
            hpresent_residual (Finset.mem_sdiff.mpr ⟨hc_present, hc_fixed⟩)
          have hc_not_selected : c ∉ selected τ := by
            intro hc_selected
            have hc_absent' : c ∈ absent τ :=
              hselected_absent hc_selected
            exact
              (Finset.disjoint_left.mp hpresent_absent hc_present)
                hc_absent'
          exact
            Finset.mem_union.mpr
              (Or.inl
                (Finset.mem_sdiff.mpr ⟨hc_residual, hc_not_selected⟩))
      exact ⟨fun _ => hcr, fun _ => hcw⟩
    · have hcw : c ∉ witness := hwitness_absent c hc_absent
      have hcr : c ∉ reconstructed := by
        intro hc_rec
        rcases Finset.mem_union.mp hc_rec with hc_residual | hc_fixed
        · rcases Finset.mem_sdiff.mp hc_residual with
            ⟨hc_residual_mem, hc_not_selected⟩
          have hc_absent_unselected :
              c ∈ absent τ \ selected τ :=
            Finset.mem_sdiff.mpr ⟨hc_absent, hc_not_selected⟩
          exact
            (Finset.disjoint_left.mp habsent_residual
              hc_absent_unselected) hc_residual_mem
        · have hc_present : c ∈ present τ := hfixed_present hc_fixed
          exact
            (Finset.disjoint_left.mp hpresent_absent hc_present)
              hc_absent
      exact ⟨fun h => False.elim (hcw h), fun h => False.elim (hcr h)⟩
  have htest_agreement :
      ∀ e,
        e ∈ terminal →
          (stagedOpen witness e ↔ stagedOpen reconstructed e) ∧
          (touched witness e ↔ touched reconstructed e) ∧
          (sameColorClosed witness e ↔ sameColorClosed reconstructed e) ∧
          (preTerminalRecorded witness e ↔
            preTerminalRecorded reconstructed e) := by
    intro e he
    exact
      hprefix_safety reconstructed hreconstructed_terminal e he
        (hdependency_agreement e he)
  have hscan :
      branchOfAssignment reconstructed = β ∧
        scanTranscript reconstructed = some τ :=
    hscan_deterministic reconstructed hreconstructed_terminal htest_agreement
  exact ⟨hdependency_agreement, hreconstructed_terminal, htest_agreement, hscan⟩
