import Tablet.ClosedPairsBound
import Tablet.FixedSetHistoryCellAdaptiveBranchPartition
import Tablet.FixedSetHistoryCellBranchTranscriptSummation
import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellFixedCylinderCharge
import Tablet.FixedSetHistoryCellRealizedPairBranchTranscriptSum
import Tablet.FixedSetHistoryCellGlobalRedExceptionalWitness
import Tablet.FixedSetHistoryCellBlueSupportLabels
import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRedCellCylinderMass
import Tablet.FixedSetHistoryCellRedCompatibleCompletionBlocks
import Tablet.FixedSetHistoryCellRedCompatibleAssignmentSupportExhaustion
import Tablet.FixedSetHistoryCellRedFixedCountCellSummation
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellMixedBranchTranscriptWeightPackage
import Tablet.FixedSetHistoryCellFixedBJResidualPartitionData
import Tablet.FixedSetHistoryCellFixedBJResidualDecisionTreeSupport
import Tablet.FixedSetHistoryCellFixedBJResidualReleasedBlockData
import Tablet.FixedSetHistoryCellFixedBJResidualScanData
import Tablet.FixedSetHistoryCellFixedBJResidualScanInterface
import Tablet.FixedSetHistoryCellFixedBJResidualSingleScanStability
import Tablet.FixedSetHistoryCellFixedBJResidualOwnerConstruction
import Tablet.FixedSetHistoryCellFixedBJResidualLeafCertificate
import Tablet.FixedSetHistoryCellFixedBJResidualProductTreeOwnerPackage
import Tablet.FixedSetHistoryCellRedResidualTreeNormalization
import Tablet.FixedSetHistoryCellRedResidualLeafConstruction
import Tablet.FixedSetHistoryCellRedSelectedAbsenceSiblingPruning
import Tablet.FixedSetHistoryCellRedSupportLabels
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

-- [TABLET NODE: FixedSetHistoryCellFixedCountRedWeightSum]

theorem FixedSetHistoryCellFixedCountRedWeightSum :
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
      uB ≤ uR →
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
            (Nat.choose NR uR : ℝ) * p ^ uR *
              (Nat.choose NB uB : ℝ) * p ^ uB *
                Real.rpow ((1 : ℝ) - p)
                  (max 0 (a - (uR : ℝ) - (uB : ℝ))) := by
-- BODY
  classical
  intro n m k ℓR ℓB p ε ε1 ε2 I hist recorded terminal order rep uR uB
    decEdge decRed decBlue hε1_nonneg hε1_le_one hp_nonneg hp_half
    hIcard hhist_rep hprojection hhist_cylinder hrecorded_terminal
    hterminal_universe horder_nodup horder_terminal hterminal_not_recorded
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
        (Nat.choose NR uR : ℝ) * p ^ uR *
          (Nat.choose NB uB : ℝ) * p ^ uB *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uR : ℝ) - (uB : ℝ)))
  obtain ⟨NR0, hNR0_bound, hglobal_red⟩ :=
    FixedSetHistoryCellGlobalRedExceptionalWitness
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
                    | Sum.inl _ => True
                    | Sum.inr _ =>
                        (TwoBiteEdgeCoordinateValue ω e ↔
                          TwoBiteEdgeCoordinateValue branch e)) →
                TwoBiteRegularityEvent (k := k) ε ε1 ε2 ω →
                  ∀ e,
                    e ∈ TwoBiteStagedOpenPairs ω ε I →
                    TwoBiteEdgeCoordinateValue ω e →
                    (match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) →
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
      ⟨NR, hNR_bound, RedLabel, instRedLabel, hred_label_count,
        branchRedSupport, hbranch_red_support⟩ :=
    @FixedSetHistoryCellRedSupportLabels n m k uR p ε ε1 ε2
      I hist targetHist recorded terminal decRed decBlue hglobal_red_package
      htargetHist_hist htargetHist_regular htargetHist_indep
      htargetHist_red_count
  letI : Fintype RedLabel := instRedLabel
  have hhist_embedding :
      ∀ ω : TwoBiteSample n m p, hist ω → ∀ x : Fin n, ω.2.2 x = rep.2.2 x := by
    intro ω hω x
    exact ((hhist_cylinder ω).mp hω).1 x
  obtain ⟨NB, hNB_bound, blueSupportLabels, hblue_label_count,
      hblue_labels, hblue_support_cover⟩ :=
    @FixedSetHistoryCellBlueSupportLabels n m k ℓR ℓB uB p ε
      I hist targetHist terminal rep decBlue hIcard hhist_embedding
      hprojection htargetHist_hist hstaged_terminal htargetHist_blue_count
  have htargetHist_open_count :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω → a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
    intro ω hω
    exact hopen_lower ω hω.1.1.2 (hprojection ω hω.2)
  have htargetHist_blue_label :
      ∀ ω : TwoBiteSample n m p,
        targetHist ω →
          ∃ B,
            B ∈ blueSupportLabels ∧
            B =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) := by
    intro ω hω
    exact ⟨_, hblue_support_cover ω hω, rfl⟩
  have htargetHist_branch_red :
      ∀ branch ω : TwoBiteSample n m p,
        targetHist ω →
        hist branch →
        (∀ e,
          e ∈ terminal →
            match e with
            | Sum.inl _ => True
            | Sum.inr _ =>
                (TwoBiteEdgeCoordinateValue ω e ↔
                  TwoBiteEdgeCoordinateValue branch e)) →
          ∃ J : RedLabel,
            branchRedSupport branch J =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) := by
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
      ⟨BranchLabel, instBranchLabel, blueTrace, redSupport, branchOfLabel,
        transcriptLabels, cellEvent, hbranch_label_hist, hredSupport_eq,
        hblueTrace_data, hblueTrace_functional, hcell_cover,
        hcell_geometry_full⟩ :=
    @FixedSetHistoryCellRedBranchTranscriptCells n m uR uB p ε a
      I hist targetHist recorded terminal order blueSupportLabels RedLabel
      instRedLabel branchRedSupport decRed decBlue hp_nonneg hp_half horder_nodup
      horder_terminal hterminal_not_recorded hrecorded_in_universe
      hterminal_in_universe htargetHist_hist hstaged_terminal
      hprefix_safety_for_branch hblue_labels htargetHist_open_count
      htargetHist_blue_label htargetHist_branch_red htargetHist_red_count
  rcases hcell_geometry_full with
    ⟨hcell_geometry_full, cellRealized, assignmentCompatible,
      hrealized_geometry, hcompat_forward, hcompat_inj, hpaper_tree⟩
  letI : Fintype BranchLabel := instBranchLabel
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  have hfixed_BJ_residual_certificate :
      ∀ B,
        B ∈ blueSupportLabels →
          ∀ J : RedLabel,
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
                              p ^ (τ.1.card - uR - uB) *
                                  ((1 : ℝ) - p) ^
                                    (τ.2.1.card - τ.2.2.card)
                        ≤ residualLeafMass (residualLeaf β τ) := by
    intro B hB J
    sorry
  have hcell_geometry_for_package :
      ∀ B,
        B ∈ blueSupportLabels →
          ∀ J : RedLabel,
            ∀ β : BranchLabel,
              ∀ τ,
                τ ∈ transcriptLabels →
                  ∀ ω : TwoBiteSample n m p,
                    cellEvent B J β τ ω →
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
                        ≤ ((τ.2.2).card : ℝ) ∧
                      (∀ e,
                        e ∈ terminal →
                          (match e with
                          | Sum.inl _ => False
                          | Sum.inr _ => True) →
                            (TwoBiteEdgeCoordinateValue ω e ↔
                              e ∈ blueTrace β)) ∧
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
    FixedSetHistoryCellMixedBranchTranscriptWeightPackage
      (n := n) (m := m) (uR := uR) (uB := uB) (p := p) (a := a)
      hist target terminal order blueSupportLabels blueTrace transcriptLabels
      redSupport cellEvent hp_nonneg hp_half horder_nodup
      horder_terminal hproduct_law hblue_labels hblueTrace_functional
      hcell_geometry_for_package cellRealized hrealized_geometry
      assignmentCompatible hcompat_forward hcompat_inj
      hfixed_BJ_residual_certificate hpaper_tree
  refine ⟨NR, NB, hNR_bound, hNB_bound, ?_⟩
  exact
    FixedSetHistoryCellRedFixedCountCellSummation
      (n := n) (m := m) (uR := uR) (uB := uB) (NR := NR) (NB := NB)
      (p := p) (a := a)
      hist target terminal blueSupportLabels transcriptLabels redSupport
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
