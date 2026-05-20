import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Tablet.FinsetPowersetCylinderMass
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellBlueReleasedCylinderPacking
import Tablet.FixedSetHistoryCellSelectedAbsencePowSplit
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellBlueFixedBJResidualPartitionData]

theorem FixedSetHistoryCellBlueFixedBJResidualPartitionData :
    ∀ {n m uR uB : ℕ} {p a : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [Fintype BranchLabel]
      (redTrace :
        BranchLabel →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (transcriptLabels :
        Finset
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {BlueLabel : Type} [Fintype BlueLabel]
      (J : BlueLabel)
      (blueSupport :
        BranchLabel →
          BlueLabel →
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
          Prop),
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
      B.card = uR →
      B ⊆ terminal →
      (∀ e,
        e ∈ B →
          match e with
          | Sum.inl _ => True
          | Sum.inr _ => False) →
      (∀ β β' : BranchLabel,
        (∀ e,
          e ∈ terminal →
            (match e with
            | Sum.inl _ => True
            | Sum.inr _ => False) →
              (e ∈ redTrace β ↔ e ∈ redTrace β')) →
          β = β') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            (blueSupport β J).card = uB ∧
            blueSupport β J ⊆ terminal ∧
            (∀ e,
              e ∈ blueSupport β J →
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True) ∧
            τ.1 ⊆ terminal ∧
            τ.2.1 ⊆ terminal ∧
            Disjoint τ.1 τ.2.1 ∧
            B ∪ blueSupport β J ⊆ τ.1 ∧
            (∀ e,
              e ∈ terminal →
                (match e with
                | Sum.inl _ => True
                | Sum.inr _ => False) →
                  (e ∈ redTrace β ↔ e ∈ τ.1) ∧
                  (e ∉ redTrace β ↔ e ∈ τ.2.1)) ∧
            τ.2.2 ⊆ τ.2.1 ∧
            max 0 (a - (uB : ℝ) - (uR : ℝ))
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
                      | Sum.inl _ => True
                      | Sum.inr _ => False) →
                        (e ∈ redTrace β ↔ e ∈ A)) →
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
      (releasedBlock :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            releasedBlock β τ ⊆ terminal.powerset) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ∈ releasedBlock β τ →
          A ⊆ terminal ∧
            assignmentCompatible
              ((A \ τ.2.2) ∪ B ∪ blueSupport β J) β τ) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              assignmentCompatible
                ((A \ τ.2.2) ∪ B ∪ blueSupport β J) β τ →
                A ∈ releasedBlock β τ) →
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
                  A ∈ releasedBlock β τ →
                    A ∉ releasedBlock β' τ') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
            terminal.powerset.filter
                (fun A =>
                  (τ.1 \ (B ∪ blueSupport β J)) ⊆ A ∧
                    Disjoint (τ.2.1 \ τ.2.2) A)
              ⊆ releasedBlock β τ) →
      ∃ assignmentMass :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → ℝ,
        ∃ releasedAssignments :
          BranchLabel →
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          ∃ releasedCylinderMass :
            BranchLabel →
              (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
              ℝ,
            (∀ A,
              A ∈ terminal.powerset →
                0 ≤ assignmentMass A) ∧
            terminal.powerset.sum assignmentMass ≤ 1 ∧
            (∀ (β : BranchLabel)
              (τ :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  releasedAssignments β τ ⊆ terminal.powerset) ∧
            (∀ (β : BranchLabel)
              (τ :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  releasedCylinderMass β τ =
                    (releasedAssignments β τ).sum assignmentMass) ∧
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
                          A ∉ releasedAssignments β' τ') ∧
            ∀ (β : BranchLabel)
              (τ :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
              τ ∈ transcriptLabels →
                cellRealized β τ →
                  p ^ (τ.1.card - uB - uR) *
                      ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
                    ≤ releasedCylinderMass β τ := by
-- BODY
  classical
  intro n m uR uB p a hist terminal order B BranchLabel _
    redTrace transcriptLabels BlueLabel _ J blueSupport cellRealized
    assignmentCompatible hp_nonneg hp_half _horder_nodup _horder_terminal
    _hproduct_law hBcard hBterminal hBblue _hredTrace_functional
    hrealized_geometry _hcompat_forward _hcompat_inj releasedBlock
    hreleased_subset _hreleased_sound _hreleased_complete
    hreleased_disjoint hreleased_cylinder
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let assignmentMass : Finset Coord → ℝ :=
    fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)
  let releasedAssignments :
      BranchLabel →
        (Finset Coord × Finset Coord × Finset Coord) →
          Finset (Finset Coord) :=
    releasedBlock
  let releasedCylinderMass :
      BranchLabel →
        (Finset Coord × Finset Coord × Finset Coord) → ℝ :=
    fun β τ => (releasedAssignments β τ).sum assignmentMass
  have hq_nonneg : 0 ≤ (1 : ℝ) - p := by
    linarith
  have hmass_nonneg :
      ∀ A,
        A ∈ terminal.powerset →
          0 ≤ assignmentMass A := by
    intro A _hA
    exact mul_nonneg (pow_nonneg hp_nonneg _) (pow_nonneg hq_nonneg _)
  have htotal_mass_eq :
      terminal.powerset.sum assignmentMass = 1 := by
    have h :=
      FinsetPowersetCylinderMass terminal (∅ : Finset Coord)
        (∅ : Finset Coord) p (by simp) (by simp) (by simp)
    simpa [assignmentMass] using h
  refine
    ⟨assignmentMass, releasedAssignments, releasedCylinderMass,
      hmass_nonneg, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_of_eq htotal_mass_eq
  · intro β τ hτ hreal
    exact hreleased_subset β τ hτ hreal
  · intro β τ _hτ _hreal
    rfl
  · intro β β' τ τ' A hτ hτ' hreal hreal' hdiff hA
    exact hreleased_disjoint β β' τ τ' A hτ hτ' hreal hreal' hdiff hA
  · intro β τ hτ hreal
    let R : Finset Coord := blueSupport β J
    let residualPresent : Finset Coord := τ.1 \ (B ∪ R)
    let residualAbsent : Finset Coord := τ.2.1 \ τ.2.2
    let cylinder : Finset (Finset Coord) :=
      terminal.powerset.filter
        (fun A => residualPresent ⊆ A ∧ Disjoint residualAbsent A)
    rcases hrealized_geometry β τ hτ hreal with
      ⟨hRcard, _hRterminal, hRred, hpresent_terminal,
        habsent_terminal, hpresent_absent, hfixed_present, _hblue_trace,
        hselected_absent, _hselected_large⟩
    have hBRdisj : Disjoint B R := by
        rw [Finset.disjoint_left]
        intro e heB heR
        cases e with
        | inl e =>
            exact hRred (Sum.inl e) heR
        | inr e =>
            exact hBblue (Sum.inr e) heB
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
    have hcylinder_subset : cylinder ⊆ releasedAssignments β τ := by
      simpa [cylinder, residualPresent, residualAbsent, releasedAssignments, R]
        using hreleased_cylinder β τ hτ hreal
    have hcylinder_sum_product :
        cylinder.sum assignmentMass =
          p ^ residualPresent.card *
            ((1 : ℝ) - p) ^ residualAbsent.card := by
      simpa [cylinder, residualPresent, residualAbsent, assignmentMass] using
        FinsetPowersetCylinderMass terminal residualPresent residualAbsent p
          hresidualPresent_terminal hresidualAbsent_terminal
          hresidual_disjoint
    have hcylinder_sum_le_block :
        cylinder.sum assignmentMass ≤
          (releasedAssignments β τ).sum assignmentMass := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hcylinder_subset ?_
      intro A hAblock _hAoutside
      exact hmass_nonneg A (hreleased_subset β τ hτ hreal hAblock)
    have hfixed_card : (B ∪ R).card = uR + uB := by
      rw [Finset.card_union_of_disjoint hBRdisj, hBcard, hRcard]
    have hresidualPresent_card :
        residualPresent.card = τ.1.card - uB - uR := by
      have hsdiff := Finset.card_sdiff_of_subset hfixed_present
      calc
        residualPresent.card = τ.1.card - (B ∪ R).card := by
          simpa [residualPresent, R] using hsdiff
        _ = τ.1.card - (uB + uR) := by
          rw [hfixed_card, Nat.add_comm]
        _ = τ.1.card - uB - uR := by
          rw [Nat.sub_sub]
    have hresidualAbsent_card :
        residualAbsent.card = τ.2.1.card - τ.2.2.card := by
      simpa [residualAbsent] using
        Finset.card_sdiff_of_subset hselected_absent
    calc
      p ^ (τ.1.card - uB - uR) *
          ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
          =
          p ^ residualPresent.card *
            ((1 : ℝ) - p) ^ residualAbsent.card := by
            rw [hresidualPresent_card, hresidualAbsent_card]
      _ = cylinder.sum assignmentMass := hcylinder_sum_product.symm
      _ ≤ (releasedAssignments β τ).sum assignmentMass :=
          hcylinder_sum_le_block
