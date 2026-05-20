import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Tablet.FixedSetHistoryCellFixedBJResidualCertificateConstruction
import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.FixedSetHistoryCellFixedBJResidualProductTreePacking
import Tablet.FixedSetHistoryCellBlueBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedReleasedCylinderPacking
import Tablet.FixedSetHistoryCellRedResidualLeafProductTree
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellRedTermwiseCylinderDomination
import Tablet.FinsetBlueFiberRedSupportMass
import Tablet.FinsetBlueSupportMassBound
import Tablet.TwoBiteConditionalIntersectionBound
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: FixedSetHistoryCellBlueMixedBranchTranscriptWeightPackage]

theorem FixedSetHistoryCellBlueMixedBranchTranscriptWeightPackage :
    ∀ {n m uR uB : ℕ} {p a : ℝ}
      (hist target : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (redSupportLabels :
        Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
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
      (blueSupport :
        BranchLabel →
          BlueLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (cellEvent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          TwoBiteSample n m p → Prop),
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
      (∀ B,
        B ∈ redSupportLabels →
          B.card = uR ∧
          B ⊆ terminal ∧
          ∀ e,
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
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  ∀ ω : TwoBiteSample n m p,
                    cellEvent B J β τ ω →
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
                        ≤ ((τ.2.2).card : ℝ) ∧
                      (∀ e,
                        e ∈ terminal →
                          (match e with
                          | Sum.inl _ => True
                          | Sum.inr _ => False) →
                            (TwoBiteEdgeCoordinateValue ω e ↔
                              e ∈ redTrace β)) ∧
                      (∀ e,
                        e ∈ τ.1 →
                          TwoBiteEdgeCoordinateValue ω e) ∧
                      (∀ e,
                        e ∈ τ.2.1 →
                          ¬ TwoBiteEdgeCoordinateValue ω e)) →
      (cellRealized :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  cellRealized B J β τ →
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
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ A β τ,
              A ⊆ terminal →
                τ ∈ transcriptLabels →
                  cellRealized B J β τ →
                    assignmentCompatible A B J β τ →
                      τ.1 ⊆ A ∧
                      Disjoint (τ.2.1 \ τ.2.2) A ∧
                      ∀ e,
                        e ∈ terminal →
                          e ∉ τ.2.2 →
                            (match e with
                            | Sum.inl _ => True
                            | Sum.inr _ => False) →
                              (e ∈ redTrace β ↔ e ∈ A)) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ A β β' τ τ',
              A ⊆ terminal →
                τ ∈ transcriptLabels →
                  τ' ∈ transcriptLabels →
                    cellRealized B J β τ →
                      cellRealized B J β' τ' →
                        assignmentCompatible A B J β τ →
                          assignmentCompatible A B J β' τ' →
                            β = β' ∧ τ = τ') →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
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
                      (Finset.univ : Finset ResidualLeaf).sum
                          residualLeafMass
                        ≤ 1 ∧
                      (∀ β β' : BranchLabel,
                        ∀ τ τ',
                          τ ∈ transcriptLabels →
                            τ' ∈ transcriptLabels →
                              cellRealized B J β τ →
                                cellRealized B J β' τ' →
                                  residualLeaf β τ = residualLeaf β' τ' →
                                    β = β' ∧ τ = τ') ∧
                      ∀ β : BranchLabel,
                        ∀ τ,
                          τ ∈ transcriptLabels →
                            cellRealized B J β τ →
                              p ^ (τ.1.card - uB - uR) *
                                  ((1 : ℝ) - p) ^
                                    (τ.2.1.card - τ.2.2.card)
                                ≤ residualLeafMass (residualLeaf β τ)) →
      (∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∀ β,
              ∀ τ,
                τ ∈ transcriptLabels →
                  ¬ cellRealized B J β τ →
                    ∀ ω : TwoBiteSample n m p,
                      ¬ cellEvent B J β τ ω) →
      ∃ cellWeight :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          ℝ,
        (∀ B,
          B ∈ redSupportLabels →
            ∀ J : BlueLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    0 ≤ cellWeight B J β τ) ∧
        (∀ B,
          B ∈ redSupportLabels →
            ∀ J : BlueLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    cellWeight B J β τ
                      ≤
                      p ^ τ.1.card *
                        ((1 : ℝ) - p) ^ τ.2.1.card) ∧
        (∀ B,
          B ∈ redSupportLabels →
            ∀ J : BlueLabel,
              ∀ β : BranchLabel,
                ∀ τ,
                  τ ∈ transcriptLabels →
                    TwoBiteEventProbability n m p
                        (fun ω =>
                          target ω ∧ hist ω ∧
                            cellEvent B J β τ ω)
                      ≤
                      TwoBiteEventProbability n m p hist *
                        cellWeight B J β τ) ∧
        (∀ B,
          B ∈ redSupportLabels →
            ∀ J : BlueLabel,
              (Finset.univ : Finset BranchLabel).sum
                  (fun β =>
                    transcriptLabels.sum
                      (fun τ => cellWeight B J β τ))
                ≤
                p ^ uB * p ^ uR *
                  Real.rpow ((1 : ℝ) - p)
                    (max 0 (a - (uB : ℝ) - (uR : ℝ)))) := by
-- BODY
  classical
  intro n m uR uB p a hist target terminal order redSupportLabels
    BranchLabel _ redTrace transcriptLabels BlueLabel _ blueSupport cellEvent
    hp_nonneg hp_half horder_nodup horder_terminal hproduct_law hblue_labels
    _hredTrace_functional hcell_geometry cellRealized hrealized_geometry
    assignmentCompatible _hcompat_forward _hcompat_inj hresidual_certificate
    hnonrealized_empty
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let q : ℝ := (1 : ℝ) - p
  let fixedFactor : ℝ :=
    p ^ uB * p ^ uR *
      Real.rpow q (max 0 (a - (uB : ℝ) - (uR : ℝ)))
  let cellWeight :
      Finset Coord → BlueLabel → BranchLabel → Transcript → ℝ :=
    fun B J β τ =>
      if B ∈ redSupportLabels ∧ τ ∈ transcriptLabels ∧
          cellRealized B J β τ then
        p ^ τ.1.card * q ^ τ.2.1.card
      else
        0
  have hp_le_one : p ≤ 1 := by
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  have hsample_nonneg :
      ∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω := by
    intro ω
    exact TwoBiteSampleWeightNonnegative ω hp_nonneg hp_le_one
  have hprob_nonneg :
      ∀ E : TwoBiteSample n m p → Prop,
        0 ≤ TwoBiteEventProbability n m p E := by
    intro E
    unfold TwoBiteEventProbability
    exact Finset.sum_nonneg (by
      intro ω _hω
      exact hsample_nonneg ω)
  have hprob_mono :
      ∀ {E F : TwoBiteSample n m p → Prop},
        (∀ ω, E ω → F ω) →
          TwoBiteEventProbability n m p E ≤
            TwoBiteEventProbability n m p F := by
    intro E F hEF
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω _hωF _hωnotE
        exact hsample_nonneg ω)
  have hcylinder_nonneg :
      ∀ τ : Transcript, 0 ≤ p ^ τ.1.card * q ^ τ.2.1.card := by
    intro τ
    exact mul_nonneg (pow_nonneg hp_nonneg _) (pow_nonneg hq_nonneg _)
  have hfixedFactor_nonneg : 0 ≤ fixedFactor := by
    dsimp [fixedFactor]
    exact
      mul_nonneg
        (mul_nonneg (pow_nonneg hp_nonneg _) (pow_nonneg hp_nonneg _))
        (Real.rpow_nonneg hq_nonneg _)
  refine ⟨cellWeight, ?_, ?_, ?_, ?_⟩
  · intro B hB J β τ hτ
    by_cases hreal : cellRealized B J β τ
    · have hnonneg := hcylinder_nonneg τ
      simpa [cellWeight, hB, hτ, hreal] using hnonneg
    · simp [cellWeight, hreal]
  · intro B hB J β τ hτ
    by_cases hreal : cellRealized B J β τ
    · simp [cellWeight, hB, hτ, hreal, q]
    · have hnonneg := hcylinder_nonneg τ
      simpa [cellWeight, hB, hτ, hreal, q] using hnonneg
  · intro B hB J β τ hτ
    by_cases hreal : cellRealized B J β τ
    · have hweight_eq :
          cellWeight B J β τ = p ^ τ.1.card * q ^ τ.2.1.card := by
        simp [cellWeight, hB, hτ, hreal]
      rw [hweight_eq]
      rcases hrealized_geometry B hB J β τ hτ hreal with
        ⟨_hRcard, _hRsub, _hRred, hPsub, hAsub, hDisj, _hMandatory,
          _hBlueTranscript, _hZsub, _hZlarge⟩
      let cylinder : TwoBiteSample n m p → Prop :=
        fun ω =>
          (∀ e, e ∈ τ.1 → TwoBiteEdgeCoordinateValue ω e) ∧
            (∀ e, e ∈ τ.2.1 → ¬ TwoBiteEdgeCoordinateValue ω e)
      have hcyl_cond :
          TwoBiteConditionalProbability n m p cylinder hist
            ≤ p ^ τ.1.card * q ^ τ.2.1.card := by
        dsimp [cylinder, q]
        exact
          FixedSetHistoryCellFixedCylinderCharge
            hist terminal τ.1 τ.2.1 hp_nonneg hp_le_one hPsub hAsub hDisj
            hproduct_law
      have hcyl_event :
          TwoBiteEventProbability n m p (fun ω => cylinder ω ∧ hist ω)
            ≤
            TwoBiteEventProbability n m p hist *
              min (1 : ℝ) (p ^ τ.1.card * q ^ τ.2.1.card) := by
        exact
          TwoBiteConditionalIntersectionBound
            (n := n) (m := m) (p := p)
            (cellBound := TwoBiteEventProbability n m p hist)
            (condBound := p ^ τ.1.card * q ^ τ.2.1.card)
            (event := cylinder) (condition := hist)
            hsample_nonneg (hprob_nonneg hist) (hcylinder_nonneg τ)
            le_rfl hcyl_cond
      have htarget_cell_subset :
          TwoBiteEventProbability n m p
              (fun ω =>
                target ω ∧ hist ω ∧ cellEvent B J β τ ω)
            ≤
            TwoBiteEventProbability n m p (fun ω => cylinder ω ∧ hist ω) := by
        exact hprob_mono (by
          intro ω hω
          rcases hcell_geometry B hB J β τ hτ ω hω.2.2 with
            ⟨_hRcard, _hRsub, _hRred, _hPsub, _hAsub, _hDisj,
              _hMandatory, _hBlueTranscript, _hZsub, _hZlarge, _hBlueOmega,
              hPresent, hAbsent⟩
          exact ⟨⟨hPresent, hAbsent⟩, hω.2.1⟩)
      have hmin_to_cylinder :
          TwoBiteEventProbability n m p hist *
              min (1 : ℝ) (p ^ τ.1.card * q ^ τ.2.1.card)
            ≤
            TwoBiteEventProbability n m p hist *
              (p ^ τ.1.card * q ^ τ.2.1.card) := by
        exact
          mul_le_mul_of_nonneg_left
            (min_le_right (1 : ℝ) (p ^ τ.1.card * q ^ τ.2.1.card))
            (hprob_nonneg hist)
      exact le_trans htarget_cell_subset (le_trans hcyl_event hmin_to_cylinder)
    · have hweight_eq : cellWeight B J β τ = 0 := by
        simp [cellWeight, hB, hτ, hreal]
      rw [hweight_eq, mul_zero]
      have hprob_zero :
          TwoBiteEventProbability n m p
              (fun ω =>
                target ω ∧ hist ω ∧ cellEvent B J β τ ω) = 0 := by
        apply le_antisymm
        · have hle_false :
              TwoBiteEventProbability n m p
                  (fun ω =>
                    target ω ∧ hist ω ∧ cellEvent B J β τ ω)
                ≤
                TwoBiteEventProbability n m p
                  (fun _ω : TwoBiteSample n m p => False) := by
            exact hprob_mono (by
              intro ω hω
              exact (hnonrealized_empty B hB J β τ hτ hreal ω) hω.2.2)
          have hfalse_zero :
              TwoBiteEventProbability n m p
                  (fun _ω : TwoBiteSample n m p => False) = 0 := by
            unfold TwoBiteEventProbability
            simp
          simpa [hfalse_zero] using hle_false
        · exact hprob_nonneg _
      simp [hprob_zero]
  · intro B hB J
    rcases hblue_labels B hB with ⟨hBcard, hBterm, hBblue⟩
    obtain
        ⟨ResidualLeaf, instResidualLeaf, instResidualLeafEq, residualLeaf,
          residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj,
          hleaf_dom⟩ :=
      hresidual_certificate B hB J
    letI : Fintype ResidualLeaf := instResidualLeaf
    letI : DecidableEq ResidualLeaf := instResidualLeafEq
    let blueCoord : Coord → Prop :=
      fun e =>
        match e with
        | Sum.inl _ => True
        | Sum.inr _ => False
    let blueSupportJ : BranchLabel → Finset Coord :=
      fun β => blueSupport β J
    let present : Transcript → Finset Coord := fun τ => τ.1
    let absent : Transcript → Finset Coord := fun τ => τ.2.1
    let selected : Transcript → Finset Coord := fun τ => τ.2.2
    let realizedJ : BranchLabel → Transcript → Prop :=
      fun β τ => cellRealized B J β τ
    have hgeom_pack :
        ∀ β τ,
          τ ∈ transcriptLabels →
            realizedJ β τ →
              (blueSupportJ β).card = uB ∧
              blueSupportJ β ⊆ terminal ∧
              Disjoint B (blueSupportJ β) ∧
              present τ ⊆ terminal ∧
              absent τ ⊆ terminal ∧
              Disjoint (present τ) (absent τ) ∧
              B ∪ blueSupportJ β ⊆ present τ ∧
              (∀ e,
                e ∈ terminal →
                  blueCoord e →
                    (e ∈ redTrace β ↔ e ∈ present τ) ∧
                    (e ∉ redTrace β ↔ e ∈ absent τ)) ∧
              selected τ ⊆ absent τ ∧
              max 0 (a - (uB : ℝ) - (uR : ℝ))
                ≤ ((selected τ).card : ℝ) := by
      intro β τ hτ hreal
      rcases hrealized_geometry B hB J β τ hτ hreal with
        ⟨hRcard, hRsub, hRred, hPsub, hAsub, hDisj, hMandatory,
          hBlueTranscript, hZsub, hZlarge⟩
      have hBRdisj : Disjoint B (blueSupport β J) := by
        rw [Finset.disjoint_left]
        intro e heB heR
        have hblue := hBblue e heB
        have hred := hRred e heR
        cases e with
        | inl x => exact hred
        | inr x => exact hblue
      exact
        ⟨hRcard, hRsub, hBRdisj, hPsub, hAsub, hDisj, hMandatory,
          hBlueTranscript, hZsub, hZlarge⟩
    have hleaf_inj' :
        ∀ β β' : BranchLabel,
          ∀ τ τ',
            τ ∈ transcriptLabels →
              τ' ∈ transcriptLabels →
                realizedJ β τ →
                  realizedJ β' τ' →
                    residualLeaf β τ = residualLeaf β' τ' →
                      β = β' ∧ τ = τ' := by
      simpa [realizedJ] using hleaf_inj
    have hleaf_dom' :
        ∀ β τ,
          τ ∈ transcriptLabels →
            realizedJ β τ →
              p ^ ((present τ).card - uB - uR) *
                  ((1 : ℝ) - p) ^ ((absent τ).card - (selected τ).card)
                ≤ residualLeafMass (residualLeaf β τ) := by
      simpa [present, absent, selected, realizedJ] using hleaf_dom
    obtain ⟨residualMass, hres_nonneg, hres_sum, hres_dom⟩ :=
      FixedSetHistoryCellFixedBJResidualProductTreePacking
        (uR := uB) (uB := uR)
        (terminal := terminal) (B := B) (order := order)
        (transcriptLabels := transcriptLabels) (blueCoord := blueCoord)
        (blueTrace := redTrace) (redSupport := blueSupportJ)
        (present := present) (absent := absent) (selected := selected)
        (cellRealized := realizedJ) (residualLeaf := residualLeaf)
        (residualLeafMass := residualLeafMass) horder_nodup horder_terminal
        hp_nonneg hp_half hBcard hBterm hgeom_pack hleaf_nonneg hleaf_sum
        hleaf_inj' hleaf_dom'
    have hterm_le :
        ∀ β τ,
          τ ∈ transcriptLabels →
            cellWeight B J β τ ≤ fixedFactor * residualMass β τ := by
      intro β τ hτ
      by_cases hreal : cellRealized B J β τ
      · have hweight_eq :
            cellWeight B J β τ = p ^ τ.1.card * q ^ τ.2.1.card := by
          simp [cellWeight, hB, hτ, hreal]
        rw [hweight_eq]
        simpa [fixedFactor, q, present, absent, selected, realizedJ] using
          hres_dom β τ hτ hreal
      · have hweight_eq : cellWeight B J β τ = 0 := by
          simp [cellWeight, hB, hτ, hreal]
        rw [hweight_eq]
        exact mul_nonneg hfixedFactor_nonneg (hres_nonneg β τ hτ)
    calc
      (Finset.univ : Finset BranchLabel).sum
          (fun β => transcriptLabels.sum (fun τ => cellWeight B J β τ))
          ≤
          (Finset.univ : Finset BranchLabel).sum
            (fun β =>
              transcriptLabels.sum (fun τ => fixedFactor * residualMass β τ)) := by
            apply Finset.sum_le_sum
            intro β _hβ
            apply Finset.sum_le_sum
            intro τ hτ
            exact hterm_le β τ hτ
      _ =
          (Finset.univ : Finset BranchLabel).sum
            (fun β => fixedFactor * transcriptLabels.sum
              (fun τ => residualMass β τ)) := by
            apply Finset.sum_congr rfl
            intro β _hβ
            rw [← Finset.mul_sum]
      _ =
          fixedFactor *
            (Finset.univ : Finset BranchLabel).sum
              (fun β => transcriptLabels.sum (fun τ => residualMass β τ)) := by
            rw [← Finset.mul_sum]
      _ ≤ fixedFactor * 1 := by
            exact mul_le_mul_of_nonneg_left hres_sum hfixedFactor_nonneg
      _ = fixedFactor := by
            rw [mul_one]
