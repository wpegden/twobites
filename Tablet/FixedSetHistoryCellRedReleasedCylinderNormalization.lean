import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedReleasedCylinderWeightNormalization
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellSelectedAbsencePowSplit
import Tablet.FixedSetHistoryCellTerminalProductPartition

-- [TABLET NODE: FixedSetHistoryCellRedReleasedCylinderNormalization]

theorem FixedSetHistoryCellRedReleasedCylinderNormalization :
    ∀ {n m uR uB : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
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
      (openCandidate :
        BranchLabel →
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
      (branchOfAssignment :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → BranchLabel)
      (scanTranscript :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      (selectedPresentSibling :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)]
      [DecidablePred
        (fun e : Sum (Fin m × Fin m) (Fin m × Fin m) =>
          match e with
          | Sum.inl _ => False
          | Sum.inr _ => True)],
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
          (∀ e,
            e ∈ τ.2.2 →
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
          τ.2.2 ⊆ τ.2.1) →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          cellRealized β τ →
          openCandidate β ⊆ terminal ∧
          B ∪ redSupport β J ⊆ openCandidate β ∧
          τ.2.2 ⊆ openCandidate β ∧
          (∀ e,
            e ∈ openCandidate β →
              e ∈ τ.1 →
                e ∈ B ∪ redSupport β J)) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              e ∈ τ.2.2 →
                selectedPresentSibling A β τ e →
                  ∀ (β' : BranchLabel)
                    (τ' :
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
                    τ' ∈ transcriptLabels →
                      cellRealized β' τ' →
                        ¬ assignmentCompatible A β' τ') →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (assignmentCompatible A β τ ∨
                ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ↔
              (τ.1 ⊆ A ∧
                Disjoint (τ.2.1 \ τ.2.2) A ∧
                (∀ e,
                  e ∈ terminal →
                    e ∉ τ.2.2 →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)))) →
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
                  (β ≠ β' ∨ τ ≠ τ') →
                    ¬ ((assignmentCompatible A β τ ∨
                        ∃ e ∈ τ.2.2, selectedPresentSibling A β τ e) ∧
                       (assignmentCompatible A β' τ' ∨
                        ∃ e ∈ τ'.2.2, selectedPresentSibling A β' τ' e))) →
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
                (∀ e,
                  e ∈ terminal →
                    (e ∈ τ.1 → e ∈ A) ∧
                    (e ∈ τ.2.1 → e ∉ A) ∧
                    ((match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (e ∈ blueTrace β ↔ e ∈ A)))) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized β τ →
              (∀ e,
                e ∈ terminal →
                  (e ∈ τ.1 → e ∈ A) ∧
                  (e ∈ τ.2.1 → e ∉ A) ∧
                  ((match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                    (e ∈ blueTrace β ↔ e ∈ A))) →
                assignmentCompatible A β τ) →
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
                β = branchOfAssignment A ∧
                  scanTranscript A = some τ) →
      ∃ residualLeafMass :
        Option
          (BranchLabel ×
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))) → ℝ,
        (∀ leaf, 0 ≤ residualLeafMass leaf) ∧
        (Finset.univ :
          Finset
            (Option
              (BranchLabel ×
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))))).sum
            residualLeafMass ≤ 1 ∧
        ∀ (β : BranchLabel)
          (τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          τ ∈ transcriptLabels →
            cellRealized β τ →
              p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card
                ≤
                p ^ uR * p ^ uB *
                    ((1 : ℝ) - p) ^ τ.2.2.card *
                  residualLeafMass (some (β, τ)) := by
-- BODY
  classical
  intro n m uR uB p hist terminal B BranchLabel _ blueTrace
    transcriptLabels RedLabel _ J redSupport openCandidate cellRealized
    assignmentCompatible branchOfAssignment scanTranscript
    selectedPresentSibling _ _ hp hp_half hp_dist h_B_card h_B_term
    h_B_color h_blue_func h_red h_open h_sib h_span h_span_disj
    h_comp_fwd h_comp_rev h_comp_func
  have hp_le_one : p ≤ (1 : ℝ) := by
    exact le_trans hp_half (by norm_num)
  have hq_nonneg : 0 ≤ (1 : ℝ) - p := sub_nonneg.mpr hp_le_one
  let fixedFactor : ℝ := p ^ uR * p ^ uB
  have hfixed_nonneg : 0 ≤ fixedFactor := by
    exact mul_nonneg (pow_nonneg hp uR) (pow_nonneg hp uB)
  let releasedWeight :
      BranchLabel ×
        (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) → ℝ :=
    fun leaf =>
      p ^ leaf.2.1.card *
        ((1 : ℝ) - p) ^ (leaf.2.2.1.card - leaf.2.2.2.card)
  let realizedPairs :
      Finset
        (BranchLabel ×
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))) :=
    (Finset.univ.filter
      (fun leaf => leaf.2 ∈ transcriptLabels ∧ cellRealized leaf.1 leaf.2))
  have hweight_sum : realizedPairs.sum releasedWeight ≤ fixedFactor := by
    simpa [realizedPairs, releasedWeight, fixedFactor] using
      FixedSetHistoryCellRedReleasedCylinderWeightNormalization
        hist terminal B blueTrace transcriptLabels J redSupport openCandidate
        cellRealized assignmentCompatible branchOfAssignment scanTranscript
        selectedPresentSibling hp hp_half hp_dist h_B_card h_B_term h_B_color
        h_blue_func h_red h_open h_sib h_span h_span_disj h_comp_fwd
        h_comp_rev h_comp_func
  let residualLeafMass :
      Option
        (BranchLabel ×
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))) → ℝ :=
    fun leaf =>
      if fixedFactor = 0 then 0
      else
        match leaf with
        | none => 0
        | some pair =>
            if pair.2 ∈ transcriptLabels ∧ cellRealized pair.1 pair.2 then
              releasedWeight pair / fixedFactor
            else 0
  refine ⟨residualLeafMass, ?_, ?_, ?_⟩
  · intro leaf
    by_cases hzero : fixedFactor = 0
    · simp [residualLeafMass, hzero]
    · cases leaf with
      | none =>
          simp [residualLeafMass, hzero]
      | some pair =>
          by_cases hreal : pair.2 ∈ transcriptLabels ∧ cellRealized pair.1 pair.2
          · simp [residualLeafMass, hzero, hreal]
            exact div_nonneg
              (mul_nonneg (pow_nonneg hp pair.2.1.card)
                (pow_nonneg hq_nonneg
                  (pair.2.2.1.card - pair.2.2.2.card)))
              hfixed_nonneg
          · simp [residualLeafMass, hzero, hreal]
  · by_cases hzero : fixedFactor = 0
    · simp [residualLeafMass, hzero]
    · have hfixed_pos : 0 < fixedFactor := by
        exact lt_of_le_of_ne hfixed_nonneg (by
          intro h
          exact hzero h.symm)
      have hsum_filter :
          (∑ pair :
              BranchLabel ×
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
              if pair.2 ∈ transcriptLabels ∧ cellRealized pair.1 pair.2 then
                releasedWeight pair / fixedFactor
              else 0)
            =
            realizedPairs.sum (fun pair => releasedWeight pair / fixedFactor) := by
        symm
        rw [Finset.sum_filter]
      have hsum_div :
          realizedPairs.sum (fun pair => releasedWeight pair / fixedFactor)
            =
            realizedPairs.sum releasedWeight / fixedFactor := by
        simp [div_eq_mul_inv, Finset.sum_mul]
      calc
        (Finset.univ :
          Finset
            (Option
              (BranchLabel ×
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))))).sum
            residualLeafMass
            =
            ∑ pair :
              BranchLabel ×
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
              if pair.2 ∈ transcriptLabels ∧ cellRealized pair.1 pair.2 then
                releasedWeight pair / fixedFactor
              else 0 := by
            rw [Fintype.sum_option]
            simp [hzero]
        _ =
            realizedPairs.sum (fun pair => releasedWeight pair / fixedFactor) :=
            hsum_filter
        _ =
            realizedPairs.sum releasedWeight / fixedFactor := hsum_div
        _ ≤ 1 := by
            rw [div_le_iff₀ hfixed_pos]
            simpa using hweight_sum
  · intro β τ hτ hreal
    rcases h_red β τ hτ hreal with
      ⟨_hR_card, _hR_subset, _hR_color, _hZ_color, _hP_subset, _hA_subset,
        _hPA_disjoint, _hmandatory, _hblue_trace, hZ_subset⟩
    have hpow_split :
        ((1 : ℝ) - p) ^ τ.2.1.card =
          ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card) *
            ((1 : ℝ) - p) ^ τ.2.2.card := by
      exact FixedSetHistoryCellSelectedAbsencePowSplit p τ.2.1 τ.2.2 hZ_subset
    by_cases hzero : fixedFactor = 0
    · have hmem : (β, τ) ∈ realizedPairs := by
        simp [realizedPairs, hτ, hreal]
      have hsum_nonneg :
          ∀ pair ∈ realizedPairs, 0 ≤ releasedWeight pair := by
        intro pair _hpair
        exact mul_nonneg (pow_nonneg hp pair.2.1.card)
          (pow_nonneg hq_nonneg
            (pair.2.2.1.card - pair.2.2.2.card))
      have hsingle :
          releasedWeight (β, τ) ≤ realizedPairs.sum releasedWeight :=
        Finset.single_le_sum hsum_nonneg hmem
      have hsum_le_zero : realizedPairs.sum releasedWeight ≤ 0 := by
        simpa [fixedFactor, hzero] using hweight_sum
      have hreleased_nonpos : releasedWeight (β, τ) ≤ 0 :=
        le_trans hsingle hsum_le_zero
      calc
        p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card
            =
            releasedWeight (β, τ) *
              ((1 : ℝ) - p) ^ τ.2.2.card := by
            simp [releasedWeight]
            rw [hpow_split]
            ring
        _ ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hreleased_nonpos
              (pow_nonneg hq_nonneg τ.2.2.card)
        _ =
            fixedFactor *
                ((1 : ℝ) - p) ^ τ.2.2.card *
              residualLeafMass (some (β, τ)) := by
            simp [residualLeafMass, hzero]
        _ =
            p ^ uR * p ^ uB *
                ((1 : ℝ) - p) ^ τ.2.2.card *
              residualLeafMass (some (β, τ)) := by
            simp [fixedFactor]
    · have hfixed_pos : 0 < fixedFactor := by
        exact lt_of_le_of_ne hfixed_nonneg (by
          intro h
          exact hzero h.symm)
      have hmass_some :
          residualLeafMass (some (β, τ)) =
            releasedWeight (β, τ) / fixedFactor := by
        simp [residualLeafMass, hzero, hτ, hreal]
      calc
        p ^ τ.1.card * ((1 : ℝ) - p) ^ τ.2.1.card
            =
            releasedWeight (β, τ) *
              ((1 : ℝ) - p) ^ τ.2.2.card := by
            simp [releasedWeight]
            rw [hpow_split]
            ring
        _ =
            fixedFactor *
                ((1 : ℝ) - p) ^ τ.2.2.card *
              residualLeafMass (some (β, τ)) := by
            rw [hmass_some]
            field_simp [hzero]
        _ ≤
            p ^ uR * p ^ uB *
                ((1 : ℝ) - p) ^ τ.2.2.card *
              residualLeafMass (some (β, τ)) := by
            simp [fixedFactor]
