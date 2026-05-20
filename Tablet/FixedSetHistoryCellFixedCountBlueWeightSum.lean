import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellAdaptiveBranchPartition
import Tablet.FixedSetHistoryCellBranchTranscriptSummation
import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.FixedSetHistoryCellRealizedPairBranchTranscriptSum
import Tablet.FixedSetHistoryCellGlobalBlueExceptionalWitness
import Tablet.FixedSetHistoryCellRedProjectionSupportLabels
import Tablet.FixedSetHistoryCellBlueBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedCellCylinderMass
import Tablet.FixedSetHistoryCellRedCompatibleCompletionBlocks
import Tablet.FixedSetHistoryCellRedCompatibleAssignmentSupportExhaustion
import Tablet.FixedSetHistoryCellBlueFixedCountCellSummation
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellBlueMixedBranchTranscriptWeightPackage
import Tablet.FixedSetHistoryCellFixedBJResidualPartitionData
import Tablet.FixedSetHistoryCellBlueFixedBJResidualPartitionData
import Tablet.FixedSetHistoryCellFixedBJResidualDecisionTreeSupport
import Tablet.FixedSetHistoryCellBlueFixedBJResidualDecisionTreeSupport
import Tablet.FixedSetHistoryCellFixedBJResidualReleasedBlockData
import Tablet.FixedSetHistoryCellBlueFixedBJResidualReleasedBlockData
import Tablet.FixedSetHistoryCellFixedBJResidualCompatibilityFromScanData
import Tablet.FixedSetHistoryCellFixedBJResidualScanData
import Tablet.FixedSetHistoryCellFixedBJResidualScanInterface
import Tablet.FixedSetHistoryCellFixedBJResidualSingleScanStability
import Tablet.FixedSetHistoryCellFixedBJResidualOwnerConstruction
import Tablet.FixedSetHistoryCellFixedBJResidualLeafCertificate
import Tablet.FixedSetHistoryCellFixedBJResidualProductTreeOwnerPackage
import Tablet.FixedSetHistoryCellBlueFixedBJResidualProductTreeOwnerPackage
import Tablet.FixedSetHistoryCellRedResidualTreeNormalization
import Tablet.FixedSetHistoryCellRedResidualLeafConstruction
import Tablet.FixedSetHistoryCellRedSelectedAbsenceSiblingPruning
import Tablet.FixedSetHistoryCellBlueExceptionalSupportLabels
import Tablet.FixedSetHistoryCellRedSupportDeterminedByBlueTrace
import Tablet.FixedSetHistoryCellRedTwoStageResidualCertificate
import Tablet.FixedSetHistoryCellTerminalProductPartition
import Tablet.ProjectionOpenPairFunction
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteProjectionSizeEvent
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

-- [TABLET NODE: FixedSetHistoryCellFixedCountBlueWeightSum]

theorem FixedSetHistoryCellFixedCountBlueWeightSum :
    ∀ {n m k ℓR ℓB : ℕ} {p ε ε1 ε2 : ℝ}
      (I : Finset (Fin n))
      (hist : TwoBiteSample n m p → Prop)
        (recorded terminal :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (rep : TwoBiteSample n m p)
        (uR uB : ℕ)
        [∀ (ω : TwoBiteSample n m p)
          (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
          Decidable (TwoBiteEdgeCoordinateValue ω e)]
        [∀ (ω : TwoBiteSample n m p),
          DecidablePred
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)]
        [∀ (ω : TwoBiteSample n m p),
          DecidablePred
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True)],
      0 ≤ ε1 →
      ε1 ≤ 1 →
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      I.card = k →
      hist rep →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
            (ℓB := ℓB) ω I) →
      (∀ ω : TwoBiteSample n m p,
        hist ω ↔
          (∀ x : Fin n, ω.2.2 x = rep.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue rep e))) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
              e ∈ recorded) →
        (∀ e,
          e ∈ terminal ↔
            e ∈ TwoBiteTerminalCoordinateUniverse m ∧ e ∉ recorded) →
        order.Nodup →
        order.toFinset = terminal →
        TwoBiteTerminalOrderRedBeforeBlue terminal order →
        (∀ e, e ∈ terminal → e ∉ recorded) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m))
            (suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m))),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                  (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                    e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                  (TwoBiteProjectionPairTouched ω ε I e ↔
                    TwoBiteProjectionPairTouched ω' ε I e) ∧
                  (TwoBiteProjectionPairSameColorClosed ω I e ↔
                    TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                  (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) →
      (∀ ω : TwoBiteSample n m p,
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
        TwoBiteProjectionSizeEvent (k := k) (ℓR := ℓR)
          (ℓB := ℓB) ω I →
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
            (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
          ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      (∀ branch : TwoBiteSample n m p,
        hist branch →
          ∃ ER EB : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ER ⊆ terminal ∧
            EB ⊆ terminal ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ => True
                  | Sum.inr _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((ER.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ ER)) ∧
            (∀ ω : TwoBiteSample n m p,
              hist ω →
              (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
              (∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue branch e)) →
              (∀ e,
                e ∈ terminal →
                  match e with
                  | Sum.inl _ =>
                      (TwoBiteEdgeCoordinateValue ω e ↔
                        TwoBiteEdgeCoordinateValue branch e)
                  | Sum.inr _ => True) →
              TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                ClosedPairsBound ((EB.card : ℝ)) (3 * ε1) (k : ℝ) ∧
                (∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                  TwoBiteEdgeCoordinateValue ω e →
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                  (TwoBiteFinalGraph ω).2.2.IsIndepSet
                    (↑I : Set (Fin n)) →
                    e ∈ EB))) →
      let a : ℝ :=
        ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
          (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
      uR ≤ uB →
        ∃ NR NB : ℕ,
          (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
          (NB : ℝ) ≤ (k : ℝ) ^ 2 ∧
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ((TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω) ∧
                (((TwoBiteStagedOpenPairs ω ε I).filter
                  (fun e =>
                    TwoBiteEdgeCoordinateValue ω e ∧
                      match e with
                      | Sum.inl _ => True
                      | Sum.inr _ => False)).card = uR) ∧
                (((TwoBiteStagedOpenPairs ω ε I).filter
                  (fun e =>
                    TwoBiteEdgeCoordinateValue ω e ∧
                      match e with
                      | Sum.inl _ => False
                      | Sum.inr _ => True)).card = uB))
            hist
            ≤
            (Nat.choose NR uB : ℝ) * p ^ uB *
              (Nat.choose NB uR : ℝ) * p ^ uR *
                Real.rpow ((1 : ℝ) - p)
                  (max 0 (a - (uB : ℝ) - (uR : ℝ))) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε ε1 ε2 I hist recorded terminal order rep uR uB
      decEdge decRed decBlue hε1_nonneg hε1_le_one hp_nonneg hp_half
      hIcard hhist_rep hprojection hhist_cylinder hrecorded_terminal
      hterminal_universe horder_nodup horder_terminal hred_before_blue
      hterminal_not_recorded
      hstaged_terminal hproduct_law hprefix_safety hopen_lower
    hbranch_exception
  letI :
      ∀ (ω : TwoBiteSample n m p)
        (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
        Decidable (TwoBiteEdgeCoordinateValue ω e) := decEdge
  letI :
      ∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) := decRed
  letI :
      ∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) := decBlue
  let target : TwoBiteSample n m p → Prop :=
    fun ω =>
      ((TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
        TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω) ∧
        (((TwoBiteStagedOpenPairs ω ε I).filter
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False)).card = uR) ∧
        (((TwoBiteStagedOpenPairs ω ε I).filter
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True)).card = uB)
  let targetHist : TwoBiteSample n m p → Prop :=
    fun ω => target ω ∧ hist ω
  let a : ℝ :=
    ProjectionOpenPairFunction (ℓR : ℝ) (ℓB : ℝ)
      (k : ℝ) p (n : ℝ) - 10 * ε1 * (k : ℝ) ^ 2
  dsimp only
  intro huB_le_uR
  change
    ∃ NR NB : ℕ,
      (NR : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
      (NB : ℝ) ≤ (k : ℝ) ^ 2 ∧
      TwoBiteConditionalProbability n m p target hist
        ≤
        (Nat.choose NR uB : ℝ) * p ^ uB *
          (Nat.choose NB uR : ℝ) * p ^ uR *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uB : ℝ) - (uR : ℝ)))
  obtain ⟨NR0, hNR0_bound, hglobal_red⟩ :=
    FixedSetHistoryCellGlobalBlueExceptionalWitness
      (n := n) (m := m) (k := k) (p := p) (ε := ε)
      (ε1 := ε1) (ε2 := ε2)
      I hist recorded terminal hε1_nonneg hbranch_exception
  have hglobal_red_package :
      ∃ NR0 : ℕ,
        (NR0 : ℝ) ≤ 3 * ε1 * (k : ℝ) ^ 2 ∧
        ∀ branch : TwoBiteSample n m p,
          hist branch →
            ∃ ER : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              ER ⊆ terminal ∧
              (ER.card : ℝ) ≤ (NR0 : ℝ) ∧
              ∀ ω : TwoBiteSample n m p,
                hist ω →
                (∀ x : Fin n, ω.2.2 x = branch.2.2 x) →
                (∀ e,
                  e ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue branch e)) →
                (∀ e,
                  e ∈ terminal →
                    match e with
                    | Sum.inl _ =>
                        (TwoBiteEdgeCoordinateValue ω e ↔
                          TwoBiteEdgeCoordinateValue branch e)
                    | Sum.inr _ => True) →
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                  ∀ e,
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                    TwoBiteEdgeCoordinateValue ω e →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet
                      (↑I : Set (Fin n)) →
                    e ∈ ER :=
    ⟨NR0, hNR0_bound, hglobal_red⟩
  have htargetHist_hist :
      ∀ ω : TwoBiteSample n m p, targetHist ω → hist ω := by
    intro ω hω
    exact hω.2
  have htargetHist_regular :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω → TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω := by
    intro ω hω
    exact hω.1.1.2
  have htargetHist_indep :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω → (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) := by
    intro ω hω
    exact hω.1.1.1
  have htargetHist_red_count :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)).card = uR) := by
    intro ω hω
    exact hω.1.2.1
  have htargetHist_blue_count :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True)).card = uB) := by
    intro ω hω
    exact hω.1.2.2
  obtain
      ⟨NR, hNR_bound, BlueLabel, instBlueLabel, hred_label_count,
        branchBlueSupport, hbranch_red_support⟩ :=
    @FixedSetHistoryCellBlueExceptionalSupportLabels n m k uB p ε ε1 ε2
      I hist targetHist recorded terminal decRed decBlue hglobal_red_package
      htargetHist_hist htargetHist_regular htargetHist_indep
      htargetHist_blue_count
  letI : Fintype BlueLabel := instBlueLabel
  have hhist_embedding :
      ∀ ω : TwoBiteSample n m p, hist ω → ∀ x : Fin n, ω.2.2 x = rep.2.2 x := by
    intro ω hω x
    exact ((hhist_cylinder ω).mp hω).1 x
  obtain ⟨NB, hNB_bound, redSupportLabels, hblue_label_count,
      hblue_labels, hblue_support_cover⟩ :=
    @FixedSetHistoryCellRedProjectionSupportLabels n m k ℓR ℓB uR p ε
      I hist targetHist terminal rep decRed hIcard hhist_embedding
      hprojection htargetHist_hist hstaged_terminal htargetHist_red_count
  have htargetHist_open_count :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω → a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
    intro ω hω
    exact hopen_lower ω hω.1.1.2 (hprojection ω hω.2)
  have htargetHist_blue_label :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω →
          ∃ B,
            B ∈ redSupportLabels ∧
            B =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) := by
    intro ω hω
    exact ⟨_, hblue_support_cover ω hω, rfl⟩
  have htargetHist_branch_red :
      ∀ branch ω : TwoBiteSample n m p,
        targetHist ω →
        hist branch →
        (∀ e,
          e ∈ terminal →
            match e with
            | Sum.inl _ =>
                (TwoBiteEdgeCoordinateValue ω e ↔
                  TwoBiteEdgeCoordinateValue branch e)
            | Sum.inr _ => True) →
          ∃ J : BlueLabel,
            branchBlueSupport branch J =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) := by
    intro branch ω hω hbranch hterminal_blue
    have hω_hist : hist ω := hω.2
    have hω_pack := (hhist_cylinder ω).mp hω_hist
    have hbranch_pack := (hhist_cylinder branch).mp hbranch
    have hsame_embedding : ∀ x : Fin n, ω.2.2 x = branch.2.2 x := by
      intro x
      exact (hω_pack.1 x).trans (hbranch_pack.1 x).symm
    have hrecorded_compat :
        ∀ e,
          e ∈ recorded →
            (TwoBiteEdgeCoordinateValue ω e ↔
              TwoBiteEdgeCoordinateValue branch e) := by
      intro e he
      exact (hω_pack.2 e he).trans (hbranch_pack.2 e he).symm
    rcases hbranch_red_support branch ω hω hbranch hsame_embedding
        hrecorded_compat hterminal_blue with
      ⟨J, hJ_eq, _hJ_card, _hJ_subset, _hJ_red⟩
    exact ⟨J, hJ_eq⟩
  have hprefix_safety_for_branch :
      ∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre suffix : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                  (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                    e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                  (TwoBiteProjectionPairTouched ω ε I e ↔
                    TwoBiteProjectionPairTouched ω' ε I e) ∧
                  (TwoBiteProjectionPairSameColorClosed ω I e ↔
                    TwoBiteProjectionPairSameColorClosed ω' I e) ∧
                  (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                    e ∈ TwoBitePreTerminalRecordedPairs ω' ε I) := by
    intro ω hω pre suffix e horder ω' hsame hrec hpre
    exact hprefix_safety ω hω pre e suffix horder ω' hsame hrec hpre
  have hrecorded_in_universe :
      ∀ e,
        e ∈ recorded →
          e ∈ TwoBiteTerminalCoordinateUniverse m := by
    intro e he
    have hpre :
        e ∈ TwoBitePreTerminalRecordedPairs rep ε I :=
      (hrecorded_terminal rep hhist_rep e).mpr he
    exact (Finset.mem_filter.mp hpre).1
  have hterminal_in_universe :
      ∀ e,
        e ∈ terminal →
          e ∈ TwoBiteTerminalCoordinateUniverse m := by
    intro e he
    exact ((hterminal_universe e).mp he).1
  obtain
      ⟨BranchLabel, instBranchLabel, redTrace, blueSupport, branchOfLabel,
        transcriptLabels, cellEvent, hbranch_label_hist, hblueSupport_eq,
        hredTrace_data, hredTrace_functional, hcell_cover,
        hcell_geometry_full⟩ :=
    @FixedSetHistoryCellBlueBranchTranscriptCells n m uR uB p ε a
      I hist targetHist recorded terminal order redSupportLabels BlueLabel
      instBlueLabel branchBlueSupport decBlue decRed hp_nonneg hp_half horder_nodup
        horder_terminal hterminal_not_recorded hrecorded_in_universe
      hterminal_in_universe htargetHist_hist (by
        intro sample sample' hsample_hist hsample'_hist
        have hsample_pack := (hhist_cylinder sample).mp hsample_hist
        have hsample'_pack := (hhist_cylinder sample').mp hsample'_hist
        constructor
        · intro x
          exact (hsample_pack.1 x).trans (hsample'_pack.1 x).symm
        · intro e he
          exact (hsample_pack.2 e he).trans (hsample'_pack.2 e he).symm)
        hstaged_terminal
        hprefix_safety_for_branch hblue_labels htargetHist_open_count
      htargetHist_blue_label htargetHist_branch_red htargetHist_blue_count
  rcases hcell_geometry_full with
    ⟨hcell_geometry_full, _hcell_provenance, cellRealized,
      assignmentCompatible, hrealized_provenance, hrealized_geometry,
      hcompat_forward, hcompat_forward_full, hcompat_converse_full,
      hcompat_inj, hnonrealized⟩
  letI : Fintype BranchLabel := instBranchLabel
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  have hfixed_BJ_residual_certificate :
      ∀ B,
        B ∈ redSupportLabels →
          ∀ J : BlueLabel,
            ∃ (ResidualLeaf : Type),
              ∃ _ : Fintype ResidualLeaf,
                ∃ _ : DecidableEq ResidualLeaf,
                  ∃ residualLeaf : BranchLabel → Transcript → ResidualLeaf,
                    ∃ residualLeafMass : ResidualLeaf → ℝ,
                      (∀ leaf : ResidualLeaf, 0 ≤ residualLeafMass leaf) ∧
                      (Finset.univ : Finset ResidualLeaf).sum
                          residualLeafMass ≤
                        1 ∧
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
                        ≤ residualLeafMass (residualLeaf β τ) := by
    intro B hB J
    letI : DecidableEq BranchLabel := Classical.typeDecidableEq BranchLabel
    letI : DecidableEq Transcript := Classical.typeDecidableEq Transcript
    letI : Fintype Transcript := inferInstance
    letI :
        ∀ β : BranchLabel,
          DecidablePred (fun τ : Transcript => cellRealized B J β τ) := by
      intro β τ
      exact Classical.propDecidable _
    have hBcard : B.card = uR := (hblue_labels B hB).1
    have hBterminal : B ⊆ terminal := (hblue_labels B hB).2.1
    have hBblue :
        ∀ e,
          e ∈ B →
            match e with
            | Sum.inl _ => True
            | Sum.inr _ => False := (hblue_labels B hB).2.2
    have hfixed_geometry :
        ∀ (β : BranchLabel) (τ : Transcript),
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
                ≤ ((τ.2.2).card : ℝ) := by
      intro β τ hτ hreal
      exact hrealized_geometry B hB J β τ hτ hreal
    have hcompat_forward_BJ :
        ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
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
                          (e ∈ redTrace β ↔ e ∈ A) := by
      intro A β τ hA hτ hreal hcompat
      exact hcompat_forward B hB J A β τ hA hτ hreal hcompat
    let blueCoord : Coord → Prop :=
      fun e =>
        match e with
        | Sum.inl _ => True
        | Sum.inr _ => False
    have hcompat_forward_full_BJ :
        ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                assignmentCompatible A B J β τ →
                  ∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A) := by
      intro A β τ hA hτ hreal hcompat
      exact hcompat_forward_full B hB J A β τ hA hτ hreal hcompat
    have hcompat_inj_BJ :
        ∀ (A : Finset Coord) (β β' : BranchLabel)
          (τ τ' : Transcript),
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              τ' ∈ transcriptLabels →
                cellRealized B J β τ →
                  cellRealized B J β' τ' →
                    assignmentCompatible A B J β τ →
                      assignmentCompatible A B J β' τ' →
                        β = β' ∧ τ = τ' := by
      intro A β β' τ τ' hA hτ hτ' hreal hreal' hcompat hcompat'
      exact
        hcompat_inj B hB J A β β' τ τ' hA hτ hτ' hreal hreal'
          hcompat hcompat'
    have hgeometry_for_scan :
        ∀ (β : BranchLabel) (τ : Transcript),
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              blueSupport β J ⊆ terminal ∧
              (∀ e, e ∈ blueSupport β J → ¬ blueCoord e) ∧
              τ.1 ⊆ terminal ∧
              τ.2.1 ⊆ terminal ∧
              Disjoint τ.1 τ.2.1 ∧
              B ∪ blueSupport β J ⊆ τ.1 ∧
              (∀ e,
                e ∈ terminal →
                  blueCoord e →
                    (e ∈ redTrace β ↔ e ∈ τ.1) ∧
                    (e ∉ redTrace β ↔ e ∈ τ.2.1)) ∧
              τ.2.2 ⊆ τ.2.1 := by
      intro β τ hτ hreal
      rcases hfixed_geometry β τ hτ hreal with
        ⟨_hRcard, hRterminal, hRred, hPterminal, hAterminal, hDisjoint,
          hFixedPresent, hBlueTrace, hSelectedAbsent, _hSelectedLarge⟩
      refine
        ⟨hRterminal, ?_, hPterminal, hAterminal, hDisjoint,
          hFixedPresent, hBlueTrace, hSelectedAbsent⟩
      intro e he hblue
      cases e with
      | inl q =>
          exact hRred (Sum.inl q) he
      | inr q =>
          exact hblue
    have hscan_inputs :
        ∃ scanTranscript : Finset Coord → Option Transcript,
          (∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                    Disjoint (τ.2.1 \ τ.2.2) A →
                      scanTranscript
                          ((A \ τ.2.2) ∪ (B ∪ blueSupport β J)) =
                        some τ) ∧
          (∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  τ.1 ⊆ A →
                    Disjoint τ.2.1 A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ) ∧
          (∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  τ.1 ⊆ A →
                    Disjoint τ.2.1 A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ →
                      assignmentCompatible A B J β τ) ∧
          ∀ (A : Finset Coord) (β β' : BranchLabel)
            (τ τ' : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                τ' ∈ transcriptLabels →
                  cellRealized B J β τ →
                    cellRealized B J β' τ' →
                      (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                        Disjoint (τ.2.1 \ τ.2.2) A →
                          (τ'.1 \ (B ∪ blueSupport β' J)) ⊆ A →
                            Disjoint (τ'.2.1 \ τ'.2.2) A →
                              assignmentCompatible
                                ((A \ τ.2.2) ∪
                                  (B ∪ blueSupport β J)) B J β τ →
                              assignmentCompatible
                                ((A \ τ'.2.2) ∪
                                  (B ∪ blueSupport β' J)) B J β' τ' →
                                β = β' ∧ τ = τ' := by
      let scanTranscript : Finset Coord → Option Transcript :=
        fun A =>
          if h :
              ∃ owner : BranchLabel × Transcript,
                owner.2 ∈ transcriptLabels ∧
                  cellRealized B J owner.1 owner.2 ∧
                    assignmentCompatible A B J owner.1 owner.2 then
            some (Classical.choose h).2
          else
            none
      have hscan_of_compatible :
          ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  assignmentCompatible A B J β τ →
                    scanTranscript A = some τ := by
        intro A β τ hA hτ hreal hcompat
        have hexists :
            ∃ owner : BranchLabel × Transcript,
              owner.2 ∈ transcriptLabels ∧
                cellRealized B J owner.1 owner.2 ∧
                  assignmentCompatible A B J owner.1 owner.2 := by
          exact ⟨(β, τ), hτ, hreal, hcompat⟩
        have hchosen := Classical.choose_spec hexists
        have hsame :=
          hcompat_inj_BJ A (Classical.choose hexists).1 β
            (Classical.choose hexists).2 τ hA hchosen.1 hτ hchosen.2.1
            hreal hchosen.2.2 hcompat
        have hτ_eq : (Classical.choose hexists).2 = τ := hsame.2
        change
          (if h :
              ∃ owner : BranchLabel × Transcript,
                owner.2 ∈ transcriptLabels ∧
                  cellRealized B J owner.1 owner.2 ∧
                    assignmentCompatible A B J owner.1 owner.2 then
            some (Classical.choose h).2
          else
            none) = some τ
        rw [dif_pos hexists]
        simp [hτ_eq]
      have hresidual_scan_stable :
          ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                    Disjoint (τ.2.1 \ τ.2.2) A →
                      scanTranscript
                          ((A \ τ.2.2) ∪ (B ∪ blueSupport β J)) =
                        some τ := by
        intro A β τ hA hτ hreal hpresentResidual habsentResidual
        let reconstructed : Finset Coord :=
          (A \ τ.2.2) ∪ (B ∪ blueSupport β J)
        rcases hgeometry_for_scan β τ hτ hreal with
          ⟨_hRterminal, _hRnotBlue, hPterminal, _hAterminal, hDisjoint,
            hFixedPresent, hBlueTranscript, hSelectedAbsent⟩
        have hReconstructedTerminal : reconstructed ⊆ terminal := by
          intro e he
          rcases Finset.mem_union.mp he with heA | heFixed
          · exact hA (Finset.mem_sdiff.mp heA).1
          · exact hPterminal (hFixedPresent heFixed)
        have hPresentReconstructed : τ.1 ⊆ reconstructed := by
          intro e hePresent
          by_cases heFixed : e ∈ B ∪ blueSupport β J
          · exact Finset.mem_union.mpr (Or.inr heFixed)
          · have heA : e ∈ A :=
              hpresentResidual (Finset.mem_sdiff.mpr ⟨hePresent, heFixed⟩)
            have heNotSelected : e ∉ τ.2.2 := by
              intro heSelected
              exact
                (Finset.disjoint_left.mp hDisjoint hePresent)
                  (hSelectedAbsent heSelected)
            exact
              Finset.mem_union.mpr
                (Or.inl (Finset.mem_sdiff.mpr ⟨heA, heNotSelected⟩))
        have hAbsentReconstructed : Disjoint τ.2.1 reconstructed := by
          rw [Finset.disjoint_left]
          intro e heAbsent heReconstructed
          rcases Finset.mem_union.mp heReconstructed with heA | heFixed
          · rcases Finset.mem_sdiff.mp heA with ⟨heA_mem, heNotSelected⟩
            exact
              (Finset.disjoint_left.mp habsentResidual
                (Finset.mem_sdiff.mpr ⟨heAbsent, heNotSelected⟩)) heA_mem
          · exact
              (Finset.disjoint_left.mp hDisjoint (hFixedPresent heFixed))
                heAbsent
        have hBlueReconstructed :
            ∀ e,
              e ∈ terminal →
                blueCoord e →
                  (e ∈ redTrace β ↔ e ∈ reconstructed) := by
          intro e heTerminal heBlue
          constructor
          · intro heTrace
            exact hPresentReconstructed
              ((hBlueTranscript e heTerminal heBlue).1.mp heTrace)
          · intro heReconstructed
            rcases Finset.mem_union.mp heReconstructed with heA | heFixed
            · rcases Finset.mem_sdiff.mp heA with ⟨heA_mem, heNotSelected⟩
              by_contra heNotTrace
              have heAbsent : e ∈ τ.2.1 :=
                (hBlueTranscript e heTerminal heBlue).2.mp heNotTrace
              exact
                (Finset.disjoint_left.mp habsentResidual
                  (Finset.mem_sdiff.mpr ⟨heAbsent, heNotSelected⟩)) heA_mem
            · exact
                (hBlueTranscript e heTerminal heBlue).1.mpr
                  (hFixedPresent heFixed)
        have hcompatReconstructed :
            assignmentCompatible reconstructed B J β τ :=
          hcompat_converse_full B hB J reconstructed β τ
            hReconstructedTerminal hτ hreal hPresentReconstructed
            hAbsentReconstructed hBlueReconstructed
        exact
          hscan_of_compatible reconstructed β τ hReconstructedTerminal hτ
            hreal hcompatReconstructed
      have hfull_scan_recognizes :
          ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  τ.1 ⊆ A →
                    Disjoint τ.2.1 A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ := by
        intro A β τ hA hτ hreal hPresent hAbsent hBlue
        have hcompatA : assignmentCompatible A B J β τ :=
          hcompat_converse_full B hB J A β τ hA hτ hreal hPresent hAbsent
            hBlue
        exact hscan_of_compatible A β τ hA hτ hreal hcompatA
      have hcompat_converse_scan :
          ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                cellRealized B J β τ →
                  τ.1 ⊆ A →
                    Disjoint τ.2.1 A →
                  (∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A)) →
                    scanTranscript A = some τ →
                      assignmentCompatible A B J β τ := by
        intro A β τ hA hτ hreal hPresent hAbsent hBlue _hscan
        exact
          hcompat_converse_full B hB J A β τ hA hτ hreal hPresent hAbsent
            hBlue
      have hfirst_mismatch_unique :
          ∀ (A : Finset Coord) (β β' : BranchLabel)
            (τ τ' : Transcript),
            A ⊆ terminal →
              τ ∈ transcriptLabels →
                τ' ∈ transcriptLabels →
                  cellRealized B J β τ →
                    cellRealized B J β' τ' →
                      (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                        Disjoint (τ.2.1 \ τ.2.2) A →
                          (τ'.1 \ (B ∪ blueSupport β' J)) ⊆ A →
                            Disjoint (τ'.2.1 \ τ'.2.2) A →
                              assignmentCompatible
                                ((A \ τ.2.2) ∪
                                  (B ∪ blueSupport β J)) B J β τ →
                                assignmentCompatible
                                  ((A \ τ'.2.2) ∪
                                    (B ∪ blueSupport β' J)) B J β' τ' →
                                  β = β' ∧ τ = τ' := by
          intro A β β' τ τ' hA hτ hτ' hreal hreal'
            hpresentResidual habsentResidual hpresentResidual'
            habsentResidual' hcompat hcompat'
          let fixed : Finset Coord := B ∪ blueSupport β J
          let fixed' : Finset Coord := B ∪ blueSupport β' J
          let recon : Finset Coord := (A \ τ.2.2) ∪ fixed
          let recon' : Finset Coord := (A \ τ'.2.2) ∪ fixed'
          rcases hfixed_geometry β τ hτ hreal with
            ⟨_hRcard, hRterminal, hRred, hPterminal, hAbsentTerminal,
              hPresentAbsent, hFixedPresent, hBlueTranscript,
              hSelectedAbsent, _hSelectedLarge⟩
          rcases hfixed_geometry β' τ' hτ' hreal' with
            ⟨_hRcard', hRterminal', hRred', hPterminal',
              hAbsentTerminal', hPresentAbsent', hFixedPresent',
              hBlueTranscript', hSelectedAbsent', _hSelectedLarge'⟩
          rcases hrealized_provenance B hB J β τ hτ hreal with
            ⟨ω, _hcell, _hTarget, hHist, hBlueSupport, hRedSupport,
              hPresentShape, hAbsentShape, hSelectedShape,
              hSelectedPrefix⟩
          rcases hrealized_provenance B hB J β' τ' hτ' hreal' with
            ⟨ω', _hcell', _hTarget', hHist', hBlueSupport',
              hRedSupport', hPresentShape', hAbsentShape',
              hSelectedShape', hSelectedPrefix'⟩
          have hHistAgree :
              (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) ∧
                ∀ e,
                  e ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω e ↔
                      TwoBiteEdgeCoordinateValue ω' e) := by
            have hω := (hhist_cylinder ω).mp hHist
            have hω' := (hhist_cylinder ω').mp hHist'
            constructor
            · intro x
              exact (hω.1 x).trans (hω'.1 x).symm
            · intro e he
              exact (hω.2 e he).trans (hω'.2 e he).symm
          have hfixed_subset_present : fixed ⊆ τ.1 := by
            simpa [fixed] using hFixedPresent
          have hfixed_subset_present' : fixed' ⊆ τ'.1 := by
            simpa [fixed'] using hFixedPresent'
          have hrec_terminal : recon ⊆ terminal := by
            intro e he
            rcases Finset.mem_union.mp he with heA | heFixed
            · exact hA (Finset.mem_sdiff.mp heA).1
            · exact hPterminal (hfixed_subset_present heFixed)
          have hrec_terminal' : recon' ⊆ terminal := by
            intro e he
            rcases Finset.mem_union.mp he with heA | heFixed
            · exact hA (Finset.mem_sdiff.mp heA).1
            · exact hPterminal' (hfixed_subset_present' heFixed)
          have hforward :=
            hcompat_forward_BJ recon β τ hrec_terminal hτ hreal hcompat
          have hforward' :=
            hcompat_forward_BJ recon' β' τ' hrec_terminal' hτ' hreal'
              hcompat'
          have hfullBlue :=
            hcompat_forward_full_BJ recon β τ hrec_terminal hτ hreal hcompat
          have hfullBlue' :=
            hcompat_forward_full_BJ recon' β' τ' hrec_terminal' hτ' hreal'
              hcompat'
          have hselected_not_rec :
              ∀ e, e ∈ τ.2.2 → e ∉ recon := by
            intro e heSelected heRec
            rcases Finset.mem_union.mp heRec with heA | heFixed
            · exact (Finset.mem_sdiff.mp heA).2 heSelected
            · exact
                (Finset.disjoint_left.mp hPresentAbsent
                  (hfixed_subset_present heFixed))
                  (hSelectedAbsent heSelected)
          have hselected_not_rec' :
              ∀ e, e ∈ τ'.2.2 → e ∉ recon' := by
            intro e heSelected heRec
            rcases Finset.mem_union.mp heRec with heA | heFixed
            · exact (Finset.mem_sdiff.mp heA).2 heSelected
            · exact
                (Finset.disjoint_left.mp hPresentAbsent'
                  (hfixed_subset_present' heFixed))
                  (hSelectedAbsent' heSelected)
          have hvalue_rec :
              ∀ e,
                e ∈ terminal →
                  (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ recon) := by
            intro e heTerminal
            constructor
            · intro hvalue
              have hePresent : e ∈ τ.1 := by
                simpa [hPresentShape, hvalue] using heTerminal
              exact hforward.1 hePresent
            · intro heRec
              by_contra hvalue
              have heAbsent : e ∈ τ.2.1 := by
                simpa [hAbsentShape, hvalue] using heTerminal
              by_cases heSelected : e ∈ τ.2.2
              · exact hselected_not_rec e heSelected heRec
              · exact
                (Finset.disjoint_left.mp hforward.2.1
                  (Finset.mem_sdiff.mpr ⟨heAbsent, heSelected⟩)) heRec
          have hvalue_rec' :
              ∀ e,
                e ∈ terminal →
                  (TwoBiteEdgeCoordinateValue ω' e ↔ e ∈ recon') := by
            intro e heTerminal
            constructor
            · intro hvalue
              have hePresent : e ∈ τ'.1 := by
                simpa [hPresentShape', hvalue] using heTerminal
              exact hforward'.1 hePresent
            · intro heRec
              by_contra hvalue
              have heAbsent : e ∈ τ'.2.1 := by
                simpa [hAbsentShape', hvalue] using heTerminal
              by_cases heSelected : e ∈ τ'.2.2
              · exact hselected_not_rec' e heSelected heRec
              · exact
                (Finset.disjoint_left.mp hforward'.2.1
                  (Finset.mem_sdiff.mpr ⟨heAbsent, heSelected⟩)) heRec
          by_cases hsame_rec : recon = recon'
          · have hcompat_same :
              assignmentCompatible recon B J β' τ' := by
                simpa [recon', hsame_rec] using hcompat'
            exact
              hcompat_inj_BJ recon β β' τ τ' hrec_terminal hτ hτ' hreal
                hreal' hcompat hcompat_same
          · let mismatch : Coord → Prop :=
              fun e => (e ∈ recon ∧ e ∉ recon') ∨ (e ∈ recon' ∧ e ∉ recon)
            have hex_mismatch :
                ∃ e, e ∈ order ∧ mismatch e := by
              by_contra hnone
              apply hsame_rec
              ext e
              constructor
              · intro heRec
                by_contra heRec'
                have heTerminal : e ∈ terminal := hrec_terminal heRec
                have heOrder : e ∈ order := by
                  have : e ∈ order.toFinset := by simpa [horder_terminal] using heTerminal
                  simpa using this
                exact hnone ⟨e, heOrder, Or.inl ⟨heRec, heRec'⟩⟩
              · intro heRec'
                by_contra heRec
                have heTerminal : e ∈ terminal := hrec_terminal' heRec'
                have heOrder : e ∈ order := by
                  have : e ∈ order.toFinset := by simpa [horder_terminal] using heTerminal
                  simpa using this
                exact hnone ⟨e, heOrder, Or.inr ⟨heRec', heRec⟩⟩
            let pBad : Coord → Bool := fun c => decide (mismatch c)
            have hfindSome : (order.find? pBad).isSome := by
              rw [List.find?_isSome]
              rcases hex_mismatch with ⟨e, heOrder, hbad⟩
              exact ⟨e, heOrder, by simpa [pBad, hbad]⟩
            let e : Coord := (order.find? pBad).get hfindSome
            have hfind_eq : order.find? pBad = some e := by
              exact Option.eq_some_of_isSome hfindSome
            have heOrder : e ∈ order :=
              List.mem_of_find?_eq_some hfind_eq
            have heBad : mismatch e := by
              have hp : pBad e := List.find?_some hfind_eq
              simpa [pBad] using hp
            rcases (List.find?_eq_some_iff_append.mp hfind_eq).2 with
              ⟨pre, suffix, hsplit, hnoBadPreBool⟩
            have heTerminal : e ∈ terminal := by
              have : e ∈ order.toFinset := by simpa using heOrder
              simpa [horder_terminal] using this
            have hsplit_prefix_eq :
                ∀ {pre₀ suffix₀ : List Coord},
                  order = pre₀ ++ e :: suffix₀ → pre₀ = pre := by
              intro pre₀ suffix₀ hsplit₀
              have hnodup_split : (pre ++ e :: suffix).Nodup := by
                simpa [hsplit] using horder_nodup
              have hnodup_append := List.nodup_append.mp hnodup_split
              have heNotPre : e ∉ pre := by
                intro hepre
                exact hnodup_append.2.2 e hepre e
                  (by simp) rfl
              have heNotSuffix : e ∉ suffix :=
                (List.nodup_cons.mp hnodup_append.2.1).1
              have hEq : pre ++ e :: suffix = pre₀ ++ e :: suffix₀ :=
                hsplit.symm.trans hsplit₀
              exact
                ((List.append_cons_inj_of_notMem
                    (x₁ := pre) (x₂ := pre₀)
                    (z₁ := suffix) (z₂ := suffix₀)
                    (a₁ := e) (a₂ := e) heNotPre heNotSuffix).mp
                  hEq).1.symm
            have hnot_bad_before :
                ∀ {pre₀ suffix₀ : List Coord} {c : Coord},
                  order = pre₀ ++ e :: suffix₀ →
                    c ∈ pre₀.toFinset →
                      ¬ mismatch c := by
              intro pre₀ suffix₀ c hsplit₀ hcpre hbadc
              have hpreEq := hsplit_prefix_eq hsplit₀
              have hcpreMain : c ∈ pre := by
                simpa [hpreEq] using hcpre
              have hnotBool := hnoBadPreBool c hcpreMain
              have hp : pBad c := by
                simpa [pBad, hbadc]
              simp [hp] at hnotBool
            have hrec_eq_before :
                ∀ {pre₀ suffix₀ : List Coord} {c : Coord},
                  order = pre₀ ++ e :: suffix₀ →
                    c ∈ pre₀.toFinset →
                      (c ∈ recon ↔ c ∈ recon') := by
              intro pre₀ suffix₀ c hsplit₀ hcpre
              have hnot := hnot_bad_before hsplit₀ hcpre
              constructor
              · intro hc
                by_contra hc'
                exact hnot (Or.inl ⟨hc, hc'⟩)
              · intro hc'
                by_contra hc
                exact hnot (Or.inr ⟨hc', hc⟩)
            have hvalue_agree_before :
                ∀ {pre₀ suffix₀ : List Coord} {c : Coord},
                  order = pre₀ ++ e :: suffix₀ →
                    c ∈ pre₀.toFinset →
                      (TwoBiteEdgeCoordinateValue ω c ↔
                        TwoBiteEdgeCoordinateValue ω' c) := by
              intro pre₀ suffix₀ c hsplit₀ hcpre
              have hcpreList : c ∈ pre₀ := by simpa using hcpre
              have hcOrder : c ∈ order := by
                rw [hsplit₀]
                exact List.mem_append.mpr (Or.inl hcpreList)
              have hcTerminal : c ∈ terminal := by
                have : c ∈ order.toFinset := by simpa using hcOrder
                simpa [horder_terminal] using this
              exact
                (hvalue_rec c hcTerminal).trans
                  ((hrec_eq_before hsplit₀ hcpre).trans
                    (hvalue_rec' c hcTerminal).symm)
            have hred_trace_eq_if_blue :
                TwoBiteCoordinateIsBlue e →
                  ∀ c,
                    c ∈ terminal →
                      TwoBiteCoordinateIsRed c →
                          (c ∈ redTrace β ↔ c ∈ redTrace β') := by
                intro heRed c hcTerminal hcBlue
                have hcPre : c ∈ pre.toFinset :=
                  hred_before_blue pre e suffix hsplit heRed c hcTerminal hcBlue
                exact
                  (hfullBlue c hcTerminal hcBlue).trans
                    ((hrec_eq_before hsplit hcPre).trans
                      (hfullBlue' c hcTerminal hcBlue).symm)
            have hfixed_for_value :
                TwoBiteEdgeCoordinateValue ω e →
                  e ∈ TwoBiteStagedOpenPairs ω ε I →
                    e ∈ fixed := by
              intro hvalue hstaged
              cases hcase : e with
              | inl q =>
                  have hstaged_q :
                      Sum.inl q ∈ TwoBiteStagedOpenPairs ω ε I := by
                    simpa [hcase] using hstaged
                  have hvalue_q :
                      TwoBiteEdgeCoordinateValue ω (Sum.inl q) := by
                    simpa [hcase] using hvalue
                  have heB : Sum.inl q ∈ B := by
                    have heFilter :
                        Sum.inl q ∈
                          {x ∈ TwoBiteStagedOpenPairs ω ε I |
                            TwoBiteEdgeCoordinateValue ω x ∧
                              match x with
                              | Sum.inl _ => True
                              | Sum.inr _ => False} := by
                      exact Finset.mem_filter.mpr
                        ⟨hstaged_q, hvalue_q, trivial⟩
                    simpa [hBlueSupport] using heFilter
                  simpa [fixed, hcase] using
                    (Finset.mem_union.mpr (Or.inl heB) :
                      Sum.inl q ∈ B ∪ blueSupport β J)
              | inr q =>
                  have hstaged_q :
                      Sum.inr q ∈ TwoBiteStagedOpenPairs ω ε I := by
                    simpa [hcase] using hstaged
                  have hvalue_q :
                      TwoBiteEdgeCoordinateValue ω (Sum.inr q) := by
                    simpa [hcase] using hvalue
                  have heR : Sum.inr q ∈ blueSupport β J := by
                    have heFilter :
                        Sum.inr q ∈
                          {x ∈ TwoBiteStagedOpenPairs ω ε I |
                            TwoBiteEdgeCoordinateValue ω x ∧
                              match x with
                              | Sum.inl _ => False
                              | Sum.inr _ => True} := by
                      exact Finset.mem_filter.mpr
                        ⟨hstaged_q, hvalue_q, trivial⟩
                    simpa [hRedSupport] using heFilter
                  simpa [fixed, hcase] using
                    (Finset.mem_union.mpr (Or.inr heR) :
                      Sum.inr q ∈ B ∪ blueSupport β J)
            have hfixed_for_value' :
                TwoBiteEdgeCoordinateValue ω' e →
                  e ∈ TwoBiteStagedOpenPairs ω' ε I →
                    e ∈ fixed' := by
              intro hvalue hstaged
              cases hcase : e with
              | inl q =>
                  have hstaged_q :
                      Sum.inl q ∈ TwoBiteStagedOpenPairs ω' ε I := by
                    simpa [hcase] using hstaged
                  have hvalue_q :
                      TwoBiteEdgeCoordinateValue ω' (Sum.inl q) := by
                    simpa [hcase] using hvalue
                  have heB : Sum.inl q ∈ B := by
                    have heFilter :
                        Sum.inl q ∈
                          {x ∈ TwoBiteStagedOpenPairs ω' ε I |
                            TwoBiteEdgeCoordinateValue ω' x ∧
                              match x with
                              | Sum.inl _ => True
                              | Sum.inr _ => False} := by
                      exact Finset.mem_filter.mpr
                        ⟨hstaged_q, hvalue_q, trivial⟩
                    simpa [hBlueSupport'] using heFilter
                  simpa [fixed', hcase] using
                    (Finset.mem_union.mpr (Or.inl heB) :
                      Sum.inl q ∈ B ∪ blueSupport β' J)
              | inr q =>
                  have hstaged_q :
                      Sum.inr q ∈ TwoBiteStagedOpenPairs ω' ε I := by
                    simpa [hcase] using hstaged
                  have hvalue_q :
                      TwoBiteEdgeCoordinateValue ω' (Sum.inr q) := by
                    simpa [hcase] using hvalue
                  have heR : Sum.inr q ∈ blueSupport β' J := by
                    have heFilter :
                        Sum.inr q ∈
                          {x ∈ TwoBiteStagedOpenPairs ω' ε I |
                            TwoBiteEdgeCoordinateValue ω' x ∧
                              match x with
                              | Sum.inl _ => False
                              | Sum.inr _ => True} := by
                      exact Finset.mem_filter.mpr
                        ⟨hstaged_q, hvalue_q, trivial⟩
                    simpa [hRedSupport'] using heFilter
                  simpa [fixed', hcase] using
                    (Finset.mem_union.mpr (Or.inr heR) :
                      Sum.inr q ∈ B ∪ blueSupport β' J)
            have hcontr_left :
                e ∈ recon → e ∉ recon' → False := by
              intro heRec heNotRec'
              have hvalue : TwoBiteEdgeCoordinateValue ω e :=
                (hvalue_rec e heTerminal).mpr heRec
              have hnotValue' : ¬ TwoBiteEdgeCoordinateValue ω' e := by
                intro hvalue'
                exact heNotRec' ((hvalue_rec' e heTerminal).mp hvalue')
              by_cases heFixed : e ∈ fixed
              · rcases Finset.mem_union.mp heFixed with heB | heR
                · have hePresent' : e ∈ τ'.1 :=
                    hfixed_subset_present'
                      (by
                        exact Finset.mem_union.mpr (Or.inl heB))
                  have hvalue' : TwoBiteEdgeCoordinateValue ω' e := by
                    have heFilter : e ∈ terminal.filter
                        (fun x => TwoBiteEdgeCoordinateValue ω' x) := by
                      simpa [hPresentShape'] using hePresent'
                    exact (Finset.mem_filter.mp heFilter).2
                  exact hnotValue' hvalue'
                · have heRed : TwoBiteCoordinateIsBlue e := by
                    cases hcase : e with
                    | inl q =>
                        have heR_q : Sum.inl q ∈ blueSupport β J := by
                          simpa [hcase] using heR
                        exact (hRred (Sum.inl q) heR_q).elim
                    | inr q => trivial
                  have hβeq : β = β' := by
                    apply hredTrace_functional
                    intro c hc hblue
                    exact hred_trace_eq_if_blue heRed c hc hblue
                  have heR' : e ∈ blueSupport β' J := by
                    simpa [hβeq] using heR
                  have hePresent' : e ∈ τ'.1 :=
                    hfixed_subset_present'
                      (Finset.mem_union.mpr (Or.inr heR'))
                  have hvalue' : TwoBiteEdgeCoordinateValue ω' e := by
                    have heFilter : e ∈ terminal.filter
                        (fun x => TwoBiteEdgeCoordinateValue ω' x) := by
                      simpa [hPresentShape'] using hePresent'
                    exact (Finset.mem_filter.mp heFilter).2
                  exact hnotValue' hvalue'
              · have heA : e ∈ A := by
                  rcases Finset.mem_union.mp heRec with heA | heFixed'
                  · exact (Finset.mem_sdiff.mp heA).1
                  · exact False.elim (heFixed heFixed')
                have heAbsent' : e ∈ τ'.2.1 := by
                  simpa [hAbsentShape', hnotValue'] using heTerminal
                by_cases heSelected' : e ∈ τ'.2.2
                · rcases hSelectedPrefix' e heSelected' with
                    ⟨hstaged', _hnotValue', pre₀, suffix₀, hsplit₀,
                      hstable⟩
                  have hpast :
                      ∀ c,
                        c ∈ pre₀.toFinset →
                          (TwoBiteEdgeCoordinateValue ω' c ↔
                            TwoBiteEdgeCoordinateValue ω c) := by
                    intro c hc
                    exact (hvalue_agree_before hsplit₀ hc).symm
                  have htests :=
                    hstable ω (fun x => (hHistAgree.1 x).symm) (by
                      intro c hc
                      exact (hHistAgree.2 c hc).symm) hpast
                  have hstaged : e ∈ TwoBiteStagedOpenPairs ω ε I :=
                    htests.1.mp hstaged'
                  exact heFixed (hfixed_for_value hvalue hstaged)
                · exact
                    (Finset.disjoint_left.mp habsentResidual'
                      (Finset.mem_sdiff.mpr ⟨heAbsent', heSelected'⟩)) heA
            have hcontr_right :
                e ∈ recon' → e ∉ recon → False := by
              intro heRec' heNotRec
              have hvalue' : TwoBiteEdgeCoordinateValue ω' e :=
                (hvalue_rec' e heTerminal).mpr heRec'
              have hnotValue : ¬ TwoBiteEdgeCoordinateValue ω e := by
                intro hvalue
                exact heNotRec ((hvalue_rec e heTerminal).mp hvalue)
              by_cases heFixed' : e ∈ fixed'
              · rcases Finset.mem_union.mp heFixed' with heB | heR'
                · have hePresent : e ∈ τ.1 :=
                    hfixed_subset_present
                      (Finset.mem_union.mpr (Or.inl heB))
                  have hvalue : TwoBiteEdgeCoordinateValue ω e := by
                    have heFilter : e ∈ terminal.filter
                        (fun x => TwoBiteEdgeCoordinateValue ω x) := by
                      simpa [hPresentShape] using hePresent
                    exact (Finset.mem_filter.mp heFilter).2
                  exact hnotValue hvalue
                · have heRed : TwoBiteCoordinateIsBlue e := by
                    cases hcase : e with
                    | inl q =>
                        have heR_q : Sum.inl q ∈ blueSupport β' J := by
                          simpa [hcase] using heR'
                        exact (hRred' (Sum.inl q) heR_q).elim
                    | inr q => trivial
                  have hβeq : β = β' := by
                    apply hredTrace_functional
                    intro c hc hblue
                    exact hred_trace_eq_if_blue heRed c hc hblue
                  have heR : e ∈ blueSupport β J := by
                    simpa [hβeq] using heR'
                  have hePresent : e ∈ τ.1 :=
                    hfixed_subset_present
                      (Finset.mem_union.mpr (Or.inr heR))
                  have hvalue : TwoBiteEdgeCoordinateValue ω e := by
                    have heFilter : e ∈ terminal.filter
                        (fun x => TwoBiteEdgeCoordinateValue ω x) := by
                      simpa [hPresentShape] using hePresent
                    exact (Finset.mem_filter.mp heFilter).2
                  exact hnotValue hvalue
              · have heA : e ∈ A := by
                  rcases Finset.mem_union.mp heRec' with heA | heFixed''
                  · exact (Finset.mem_sdiff.mp heA).1
                  · exact False.elim (heFixed' heFixed'')
                have heAbsent : e ∈ τ.2.1 := by
                  simpa [hAbsentShape, hnotValue] using heTerminal
                by_cases heSelected : e ∈ τ.2.2
                · rcases hSelectedPrefix e heSelected with
                    ⟨hstaged, _hnotValue, pre₀, suffix₀, hsplit₀,
                      hstable⟩
                  have hpast :
                      ∀ c,
                        c ∈ pre₀.toFinset →
                          (TwoBiteEdgeCoordinateValue ω c ↔
                            TwoBiteEdgeCoordinateValue ω' c) := by
                    intro c hc
                    exact hvalue_agree_before hsplit₀ hc
                  have htests :=
                    hstable ω' hHistAgree.1 hHistAgree.2 hpast
                  have hstaged' : e ∈ TwoBiteStagedOpenPairs ω' ε I :=
                    htests.1.mp hstaged
                  exact heFixed' (hfixed_for_value' hvalue' hstaged')
                · exact
                    (Finset.disjoint_left.mp habsentResidual
                      (Finset.mem_sdiff.mpr ⟨heAbsent, heSelected⟩)) heA
            rcases heBad with hbad | hbad
            · exact False.elim (hcontr_left hbad.1 hbad.2)
            · exact False.elim (hcontr_right hbad.1 hbad.2)
      exact
        ⟨scanTranscript, hresidual_scan_stable, hfull_scan_recognizes,
          hcompat_converse_scan, hfirst_mismatch_unique⟩
    rcases hscan_inputs with
      ⟨scanTranscript, hresidual_scan_stable, hfull_scan_recognizes,
        hcompat_converse, hfirst_mismatch_unique⟩
    have hcompat_forward_full_pack :
        ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                assignmentCompatible A B J β τ →
                  τ.1 ⊆ A ∧
                  Disjoint (τ.2.1 \ τ.2.2) A ∧
                  ∀ e,
                    e ∈ terminal →
                      blueCoord e →
                        (e ∈ redTrace β ↔ e ∈ A) := by
      intro A β τ hA hτ hreal hcompat
      have hforward :=
        hcompat_forward_BJ A β τ hA hτ hreal hcompat
      exact
        ⟨hforward.1, hforward.2.1,
          hcompat_forward_full_BJ A β τ hA hτ hreal hcompat⟩
    have hresidual_inputs_grouped :=
      FixedSetHistoryCellFixedBJResidualCompatibilityFromScanData
        (terminal := terminal) (B := B) (J := J)
        (blueColor := blueCoord) (blueTrace := redTrace)
        (redSupport := blueSupport) (transcriptLabels := transcriptLabels)
        (cellRealized := cellRealized)
        (assignmentCompatible := assignmentCompatible)
        (scanTranscript := scanTranscript)
        hredTrace_functional hgeometry_for_scan hcompat_forward_full_pack
        hresidual_scan_stable hfull_scan_recognizes hcompat_converse
        hfirst_mismatch_unique
    have hresidual_complete :
        ∀ (A : Finset Coord) (β : BranchLabel) (τ : Transcript),
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
              (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                Disjoint (τ.2.1 \ τ.2.2) A →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ := by
      intro A β τ hA hτ hreal hpresentResidual habsentResidual
      have hcompat :=
        hresidual_inputs_grouped.1 A β τ hA hτ hreal hpresentResidual
          habsentResidual
      simpa [Finset.union_assoc] using hcompat
    have hresidual_single_owner :
        ∀ (A : Finset Coord) (β β' : BranchLabel)
          (τ τ' : Transcript),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ →
                    assignmentCompatible
                      ((A \ τ'.2.2) ∪ B ∪ blueSupport β' J) B J β' τ' →
                      β = β' ∧ τ = τ' := by
      intro A β β' τ τ' hA hτ hτ' hreal hreal' hcompat hcompat'
      have hcompat_grouped :
          assignmentCompatible
            ((A \ τ.2.2) ∪ (B ∪ blueSupport β J)) B J β τ := by
        simpa [Finset.union_assoc] using hcompat
      have hcompat_grouped' :
          assignmentCompatible
            ((A \ τ'.2.2) ∪ (B ∪ blueSupport β' J)) B J β' τ' := by
        simpa [Finset.union_assoc] using hcompat'
      exact
        hresidual_inputs_grouped.2 A β β' τ τ' hA hτ hτ' hreal hreal'
          hcompat_grouped hcompat_grouped'
    obtain
        ⟨releasedBlock, hreleased_subset, hreleased_sound,
          hreleased_complete, hreleased_disjoint, hreleased_cylinder⟩ :=
      FixedSetHistoryCellBlueFixedBJResidualReleasedBlockData
        (n := n) (m := m) (uR := uR) (uB := uB) (p := p) (ε := ε)
        (a := a) I hist targetHist recorded terminal order B redTrace
        transcriptLabels J blueSupport cellEvent cellRealized
        assignmentCompatible horder_nodup horder_terminal hBterminal
        hfixed_geometry hcompat_forward_BJ hcompat_inj_BJ
        hresidual_complete hresidual_single_owner (hnonrealized B hB J)
    obtain
        ⟨_residualOwner, _howner_cylinder, _howner_functional,
          ResidualLeaf, instResidualLeaf, instResidualLeafEq, residualLeaf,
          residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj,
          hleaf_dom⟩ :=
      FixedSetHistoryCellBlueFixedBJResidualProductTreeOwnerPackage
        (n := n) (m := m) (uR := uR) (uB := uB) (p := p) (a := a)
        hist terminal order B redTrace transcriptLabels J blueSupport
        (cellRealized := fun β τ => cellRealized B J β τ)
        (assignmentCompatible := fun A β τ => assignmentCompatible A B J β τ)
        hp_nonneg hp_half horder_nodup horder_terminal hproduct_law
        hBcard hBterminal hBblue hredTrace_functional hfixed_geometry
        hcompat_forward_BJ hcompat_inj_BJ releasedBlock hreleased_subset
        hreleased_sound hreleased_complete hreleased_disjoint
        hreleased_cylinder
    exact
      ⟨ResidualLeaf, instResidualLeaf, instResidualLeafEq, residualLeaf,
        residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj, hleaf_dom⟩
  have hcell_geometry_for_package :
      ∀ B,
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
                          ¬ TwoBiteEdgeCoordinateValue ω e) := by
    intro B hB J β τ hτ ω hcell
    rcases hcell_geometry_full B hB J β τ hτ ω hcell with
      ⟨_hBranchHist, _hRedEq, _hBlueBranch, hRcard, hRsub, hRred,
        hPsub, hAsub, hDisj, hMandatory, hBlueTranscript, hZsub, hZlarge,
        hBlueOmega, hPresent, hAbsent⟩
    exact
      ⟨hRcard, hRsub, hRred, hPsub, hAsub, hDisj, hMandatory,
        hBlueTranscript, hZsub, hZlarge, hBlueOmega, hPresent, hAbsent⟩
  obtain
      ⟨cellWeight, hcellWeight_nonneg, hcellWeight_cylinder,
        hcellProbability, hfixed_pair_sum⟩ :=
    FixedSetHistoryCellBlueMixedBranchTranscriptWeightPackage
      (n := n) (m := m) (uB := uB) (uR := uR) (p := p) (a := a)
      hist target terminal order redSupportLabels redTrace transcriptLabels
      blueSupport cellEvent hp_nonneg hp_half horder_nodup
      horder_terminal hproduct_law hblue_labels hredTrace_functional
      hcell_geometry_for_package cellRealized hrealized_geometry
      assignmentCompatible hcompat_forward hcompat_inj
      hfixed_BJ_residual_certificate hnonrealized
  refine ⟨NR, NB, hNR_bound, hNB_bound, ?_⟩
  exact
    FixedSetHistoryCellBlueFixedCountCellSummation
      (n := n) (m := m) (uB := uB) (uR := uR) (NR := NR) (NB := NB)
      (p := p) (a := a)
      hist target terminal redSupportLabels transcriptLabels blueSupport
      cellEvent cellWeight hp_nonneg hp_half huB_le_uR hred_label_count
      hblue_label_count hblue_labels
      (by
        intro ω htargetω hhistω
        exact hcell_cover ω ⟨htargetω, hhistω⟩ hhistω)
      (by
        intro B hB J β τ hτ ω hcell
        rcases hcell_geometry_for_package B hB J β τ hτ ω hcell with
          ⟨hRcard, hRsub, hRred, hPsub, hAsub, hDisj, hMandatory,
            _hBlueTranscript, hZsub, hZlarge, _hBlueOmega, hPresent, hAbsent⟩
        exact
          ⟨hRcard, hRsub, hRred, hPsub, hAsub, hDisj, hMandatory,
            hZsub, hZlarge, hPresent, hAbsent⟩)
      hcellWeight_nonneg hcellWeight_cylinder hcellProbability
      hfixed_pair_sum
