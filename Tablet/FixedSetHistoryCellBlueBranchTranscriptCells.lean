import Tablet.FixedSetHistoryCellAdaptiveBranchPartition
import Tablet.FixedSetHistoryCellCanonicalAbsenceSelection
import Tablet.FixedSetHistoryCellFixedBJResidualOverlapConsistency
import Tablet.FinsetPowersetCylinderMass
import Tablet.FixedSetHistoryCellRISIRevealOrderScanConstruction
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellRedBranchScanInterfaceConstruction
import Tablet.FixedSetHistoryCellRedBranchOrderedRevealScanPackage
import Tablet.FixedSetHistoryCellRedResidualDeterministicScanOutputs
import Tablet.FixedSetHistoryCellRedCompatibleAssignmentDisjointness
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness
import Tablet.FixedSetHistoryCellRedPrefixScanInvariant
import Tablet.FixedSetHistoryCellRedResidualCylinderBlockMassLower
import Tablet.FixedSetHistoryCellSelectedAbsencePowSplit
import Tablet.FixedSetHistoryCellTerminalAssignmentExtension
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteTerminalCoordinateUniverse

open Classical

-- [TABLET NODE: FixedSetHistoryCellBlueBranchTranscriptCells]

theorem FixedSetHistoryCellBlueBranchTranscriptCells :
    ∀ {n m uR uB : ℕ} {p ε a : ℝ}
      (I : Finset (Fin n))
      (hist target : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (redSupportLabels :
        Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {BlueLabel : Type} [Fintype BlueLabel]
      (branchBlueSupport :
        TwoBiteSample n m p →
          BlueLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      [∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True)]
      [∀ (ω : TwoBiteSample n m p),
        DecidablePred
          (fun e =>
            TwoBiteEdgeCoordinateValue ω e ∧
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False)],
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      order.Nodup →
      order.toFinset = terminal →
      (∀ e,
        e ∈ terminal →
          e ∉ recorded) →
      (∀ e,
        e ∈ recorded →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ e,
        e ∈ terminal →
          e ∈ TwoBiteTerminalCoordinateUniverse m) →
      (∀ ω : TwoBiteSample n m p,
        target ω → hist ω) →
      (∀ ω ω' : TwoBiteSample n m p,
        hist ω →
          hist ω' →
            (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) ∧
              ∀ e,
                e ∈ recorded →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ω' e)) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ e,
            e ∈ TwoBiteStagedOpenPairs ω ε I →
              e ∈ terminal) →
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          ∀ (pre suffix :
              List (Sum (Fin m × Fin m) (Fin m × Fin m)))
            (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
            order = pre ++ e :: suffix →
              ∀ ω' : TwoBiteSample n m p,
                (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                (∀ c,
                  c ∈ recorded →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c)) →
                (∀ c,
                  c ∈ List.toFinset pre →
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
      (∀ B,
        B ∈ redSupportLabels →
          B.card = uR ∧
          B ⊆ terminal ∧
          ∀ e,
            e ∈ B →
              match e with
              | Sum.inl _ => True
              | Sum.inr _ => False) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          ∃ B,
            B ∈ redSupportLabels ∧
            B =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False)) →
      (∀ branch ω : TwoBiteSample n m p,
        target ω →
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
                    | Sum.inr _ => True)) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => False
                | Sum.inr _ => True)).card = uB)) →
      ∃ (BranchLabel : Type),
        ∃ _ : Fintype BranchLabel,
          ∃ redTrace :
            BranchLabel →
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∃ blueSupport :
              BranchLabel →
                BlueLabel →
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
              ∃ branchOfLabel :
                BranchLabel →
                  TwoBiteSample n m p,
                ∃ transcriptLabels :
                  Finset
                    (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                      Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
                  ∃ cellEvent :
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                      BlueLabel →
                      BranchLabel →
                      (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                      TwoBiteSample n m p → Prop,
            (∀ β : BranchLabel, hist (branchOfLabel β)) ∧
            (∀ (β : BranchLabel) (J : BlueLabel),
              blueSupport β J =
                branchBlueSupport (branchOfLabel β) J) ∧
            (∀ β : BranchLabel,
              redTrace β ⊆ terminal ∧
                (∀ e,
                  e ∈ redTrace β →
                    match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) ∧
                (∀ e,
                  e ∈ terminal →
                    (match e with
                    | Sum.inl _ => True
                    | Sum.inr _ => False) →
                      (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔
                        e ∈ redTrace β))) ∧
            (∀ β β' : BranchLabel,
              (∀ e,
                e ∈ terminal →
                  (match e with
                  | Sum.inl _ => True
                  | Sum.inr _ => False) →
                    (e ∈ redTrace β ↔ e ∈ redTrace β')) →
                β = β') ∧
            (∀ ω : TwoBiteSample n m p,
              target ω →
                hist ω →
                  ∃ B,
                    B ∈ redSupportLabels ∧
                      ∃ J : BlueLabel,
                        ∃ β,
                          ∃ τ,
                            τ ∈ transcriptLabels ∧
                              cellEvent B J β τ ω) ∧
            (∀ B,
              B ∈ redSupportLabels →
                ∀ J : BlueLabel,
                  ∀ β,
                    ∀ τ,
                      τ ∈ transcriptLabels →
                        ∀ ω : TwoBiteSample n m p,
                          cellEvent B J β τ ω →
                            hist (branchOfLabel β) ∧
                            blueSupport β J =
                              branchBlueSupport (branchOfLabel β) J ∧
                            (∀ e,
                              e ∈ terminal →
                                (match e with
                                | Sum.inl _ => True
                                | Sum.inr _ => False) →
                                  (TwoBiteEdgeCoordinateValue
                                    (branchOfLabel β) e ↔
                                      e ∈ redTrace β)) ∧
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
                                ¬ TwoBiteEdgeCoordinateValue ω e)) ∧
            (∀ B,
              B ∈ redSupportLabels →
                ∀ J : BlueLabel,
                  ∀ β,
                    ∀ τ,
                      τ ∈ transcriptLabels →
                        ∀ ω : TwoBiteSample n m p,
                          cellEvent B J β τ ω →
                            target ω ∧
                            hist ω ∧
                            B =
                              (TwoBiteStagedOpenPairs ω ε I).filter
                                (fun e =>
                                  TwoBiteEdgeCoordinateValue ω e ∧
                                    match e with
                                    | Sum.inl _ => True
                                    | Sum.inr _ => False) ∧
                            blueSupport β J =
                              (TwoBiteStagedOpenPairs ω ε I).filter
                                (fun e =>
                                  TwoBiteEdgeCoordinateValue ω e ∧
                                    match e with
                                    | Sum.inl _ => False
                                    | Sum.inr _ => True) ∧
                            τ.1 =
                              terminal.filter
                                (fun e => TwoBiteEdgeCoordinateValue ω e) ∧
                            τ.2.1 =
                              terminal.filter
                                (fun e => ¬ TwoBiteEdgeCoordinateValue ω e) ∧
                            τ.2.2 =
                              (TwoBiteStagedOpenPairs ω ε I).filter
                                (fun e => e ∉ blueSupport β J ∪ B) ∧
                            (∀ e,
                              e ∈ τ.2.2 →
                                e ∈ TwoBiteStagedOpenPairs ω ε I ∧
                                ¬ TwoBiteEdgeCoordinateValue ω e ∧
                                ∃ (pre suffix :
                                  List
                                    (Sum (Fin m × Fin m) (Fin m × Fin m))),
                                  order = pre ++ e :: suffix ∧
                                  ∀ ω' : TwoBiteSample n m p,
                                    (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
                                    (∀ c,
                                      c ∈ recorded →
                                        (TwoBiteEdgeCoordinateValue ω c ↔
                                          TwoBiteEdgeCoordinateValue ω' c)) →
                                    (∀ c,
                                      c ∈ List.toFinset pre →
                                        (TwoBiteEdgeCoordinateValue ω c ↔
                                          TwoBiteEdgeCoordinateValue ω' c)) →
                                      (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                                        e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
                                      (TwoBiteProjectionPairTouched ω ε I e ↔
                                        TwoBiteProjectionPairTouched
                                          ω' ε I e) ∧
                                      (TwoBiteProjectionPairSameColorClosed
                                          ω I e ↔
                                        TwoBiteProjectionPairSameColorClosed
                                          ω' I e) ∧
                                      (e ∈
                                          TwoBitePreTerminalRecordedPairs
                                            ω ε I ↔
                                        e ∈
                                          TwoBitePreTerminalRecordedPairs
                                            ω' ε I))) ∧
            ∃ cellRealized :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                BlueLabel →
                BranchLabel →
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                Prop,
              ∃ assignmentCompatible :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                  BlueLabel →
                  BranchLabel →
                  (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                  Prop,
                (∀ B,
                  B ∈ redSupportLabels →
                    ∀ J : BlueLabel,
                      ∀ β,
                        ∀ τ,
                          τ ∈ transcriptLabels →
                            cellRealized B J β τ →
                              ∃ ω : TwoBiteSample n m p,
                                cellEvent B J β τ ω ∧
                                target ω ∧
                                hist ω ∧
                                B =
                                  (TwoBiteStagedOpenPairs ω ε I).filter
                                    (fun e =>
                                      TwoBiteEdgeCoordinateValue ω e ∧
                                        match e with
                                        | Sum.inl _ => True
                                        | Sum.inr _ => False) ∧
                                blueSupport β J =
                                  (TwoBiteStagedOpenPairs ω ε I).filter
                                    (fun e =>
                                      TwoBiteEdgeCoordinateValue ω e ∧
                                        match e with
                                        | Sum.inl _ => False
                                        | Sum.inr _ => True) ∧
                                τ.1 =
                                  terminal.filter
                                    (fun e => TwoBiteEdgeCoordinateValue ω e) ∧
                                τ.2.1 =
                                  terminal.filter
                                    (fun e => ¬ TwoBiteEdgeCoordinateValue ω e) ∧
                                τ.2.2 =
                                  (TwoBiteStagedOpenPairs ω ε I).filter
                                    (fun e => e ∉ blueSupport β J ∪ B) ∧
                                (∀ e,
                                  e ∈ τ.2.2 →
                                    e ∈ TwoBiteStagedOpenPairs ω ε I ∧
                                    ¬ TwoBiteEdgeCoordinateValue ω e ∧
                                    ∃ (pre suffix :
                                      List
                                        (Sum (Fin m × Fin m) (Fin m × Fin m))),
                                      order = pre ++ e :: suffix ∧
                                      ∀ ω' : TwoBiteSample n m p,
                                        (∀ x : Fin n,
                                          ω.2.2 x = ω'.2.2 x) →
                                        (∀ c,
                                          c ∈ recorded →
                                            (TwoBiteEdgeCoordinateValue ω c ↔
                                              TwoBiteEdgeCoordinateValue
                                                ω' c)) →
                                        (∀ c,
                                          c ∈ List.toFinset pre →
                                            (TwoBiteEdgeCoordinateValue ω c ↔
                                              TwoBiteEdgeCoordinateValue
                                                ω' c)) →
                                          (e ∈
                                              TwoBiteStagedOpenPairs ω ε I ↔
                                            e ∈
                                              TwoBiteStagedOpenPairs
                                                ω' ε I) ∧
                                          (TwoBiteProjectionPairTouched
                                              ω ε I e ↔
                                            TwoBiteProjectionPairTouched
                                              ω' ε I e) ∧
                                          (TwoBiteProjectionPairSameColorClosed
                                              ω I e ↔
                                            TwoBiteProjectionPairSameColorClosed
                                              ω' I e) ∧
                                          (e ∈
                                              TwoBitePreTerminalRecordedPairs
                                                ω ε I ↔
                                            e ∈
                                              TwoBitePreTerminalRecordedPairs
                                                ω' ε I))) ∧
                (∀ B,
                  B ∈ redSupportLabels →
                    ∀ J : BlueLabel,
                      ∀ β,
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
                                ≤ ((τ.2.2).card : ℝ)) ∧
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
                                        (e ∈ redTrace β ↔ e ∈ A)) ∧
                (∀ B,
                  B ∈ redSupportLabels →
                    ∀ J : BlueLabel,
                      ∀ A β τ,
                        A ⊆ terminal →
                          τ ∈ transcriptLabels →
                            cellRealized B J β τ →
                              assignmentCompatible A B J β τ →
                                ∀ e,
                                  e ∈ terminal →
                                    (match e with
                                    | Sum.inl _ => True
                                    | Sum.inr _ => False) →
                                      (e ∈ redTrace β ↔ e ∈ A)) ∧
                (∀ B,
                  B ∈ redSupportLabels →
                    ∀ J : BlueLabel,
                      ∀ A β τ,
                        A ⊆ terminal →
                          τ ∈ transcriptLabels →
                            cellRealized B J β τ →
                              τ.1 ⊆ A →
                                Disjoint τ.2.1 A →
                                  (∀ e,
                                    e ∈ terminal →
                                      (match e with
                                      | Sum.inl _ => True
                                      | Sum.inr _ => False) →
                                        (e ∈ redTrace β ↔ e ∈ A)) →
                                    assignmentCompatible A B J β τ) ∧
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
                                                β = β' ∧ τ = τ') ∧
                        (∀ B,
                          B ∈ redSupportLabels →
                            ∀ J : BlueLabel,
                              ∀ β,
                        ∀ τ,
                          τ ∈ transcriptLabels →
                            ¬ cellRealized B J β τ →
                              ∀ ω : TwoBiteSample n m p,
                                ¬ cellEvent B J β τ ω) := by
-- BODY
  intros n m uR uB p ε a I hist target recorded terminal order redSupportLabels BlueLabel _ branchBlueSupport
  intros _ _ _hp_nonneg _hp_half horder_nodup horder_term hterminal_not_recorded hrecorded_universe hterminal_universe htarget_hist hhist_agree hhist_term hhist_pre hB_prop htarget_card htarget_B htarget_branch htarget_uB

  let firstColor (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
    match e with | Sum.inl _ => True | Sum.inr _ => False
  let blueColor (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
    match e with | Sum.inl _ => False | Sum.inr _ => True
  
  let BranchLabel := { A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) //
    A ⊆ terminal.filter firstColor ∧ ∃ ω, target ω ∧ ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A) }
  
  have instBranchLabel : Fintype BranchLabel := Fintype.ofFinite BranchLabel
  
  let redTrace (β : BranchLabel) : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := β.val
  
  let branchOfLabel (β : BranchLabel) : TwoBiteSample n m p :=
    Classical.choose β.property.2
    
  have h_branch_target (β : BranchLabel) : target (branchOfLabel β) :=
    (Classical.choose_spec β.property.2).1

  have h_branch_hist (β : BranchLabel) : hist (branchOfLabel β) :=
    htarget_hist _ (h_branch_target β)
    
  have h_branch_trace (β : BranchLabel) : ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔ e ∈ β.val) :=
    (Classical.choose_spec β.property.2).2

  let blueSupport (β : BranchLabel) (J : BlueLabel) : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    branchBlueSupport (branchOfLabel β) J

  let transcriptLabels : Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) :=
    (Finset.powerset terminal) ×ˢ (Finset.powerset terminal) ×ˢ (Finset.powerset terminal)

  let cellEvent (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) (J : BlueLabel) (β : BranchLabel) 
      (τ : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) 
      (ω : TwoBiteSample n m p) : Prop :=
    target ω ∧
    hist ω ∧
    B =
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e => TwoBiteEdgeCoordinateValue ω e ∧ firstColor e) ∧
    blueSupport β J =
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e => TwoBiteEdgeCoordinateValue ω e ∧ blueColor e) ∧
    τ.1 = terminal.filter (fun e => TwoBiteEdgeCoordinateValue ω e) ∧
    τ.2.1 = terminal.filter (fun e => ¬ TwoBiteEdgeCoordinateValue ω e) ∧
    τ.2.2 =
      (TwoBiteStagedOpenPairs ω ε I).filter
        (fun e => e ∉ blueSupport β J ∪ B) ∧
    (∀ e,
      e ∈ τ.2.2 →
        e ∈ TwoBiteStagedOpenPairs ω ε I ∧
        ¬ TwoBiteEdgeCoordinateValue ω e ∧
        ∃ (pre suffix :
          List (Sum (Fin m × Fin m) (Fin m × Fin m))),
          order = pre ++ e :: suffix ∧
          ∀ ω' : TwoBiteSample n m p,
            (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
            (∀ c,
              c ∈ recorded →
                (TwoBiteEdgeCoordinateValue ω c ↔
                  TwoBiteEdgeCoordinateValue ω' c)) →
            (∀ c,
              c ∈ List.toFinset pre →
                (TwoBiteEdgeCoordinateValue ω c ↔
                  TwoBiteEdgeCoordinateValue ω' c)) →
              (e ∈ TwoBiteStagedOpenPairs ω ε I ↔
                e ∈ TwoBiteStagedOpenPairs ω' ε I) ∧
              (TwoBiteProjectionPairTouched ω ε I e ↔
                TwoBiteProjectionPairTouched ω' ε I e) ∧
              (TwoBiteProjectionPairSameColorClosed ω I e ↔
                TwoBiteProjectionPairSameColorClosed ω' I e) ∧
              (e ∈ TwoBitePreTerminalRecordedPairs ω ε I ↔
                e ∈ TwoBitePreTerminalRecordedPairs ω' ε I)) ∧
    hist (branchOfLabel β) ∧
    blueSupport β J = branchBlueSupport (branchOfLabel β) J ∧
    (∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔ e ∈ redTrace β)) ∧
    (blueSupport β J).card = uB ∧
    blueSupport β J ⊆ terminal ∧
    (∀ e ∈ blueSupport β J, blueColor e) ∧
    τ.1 ⊆ terminal ∧
    τ.2.1 ⊆ terminal ∧
    Disjoint τ.1 τ.2.1 ∧
    B ∪ blueSupport β J ⊆ τ.1 ∧
    (∀ e ∈ terminal, firstColor e →
      (e ∈ redTrace β ↔ e ∈ τ.1) ∧
      (e ∉ redTrace β ↔ e ∈ τ.2.1)) ∧
    τ.2.2 ⊆ τ.2.1 ∧
    max 0 (a - (uB : ℝ) - (uR : ℝ)) ≤ ((τ.2.2).card : ℝ) ∧
    (∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ redTrace β)) ∧
    (∀ e ∈ τ.1, TwoBiteEdgeCoordinateValue ω e) ∧
    (∀ e ∈ τ.2.1, ¬ TwoBiteEdgeCoordinateValue ω e)

  refine ⟨BranchLabel, instBranchLabel, redTrace, blueSupport, branchOfLabel, transcriptLabels, cellEvent, 
          h_branch_hist, ?_, ?_, ?_, ?_, ?_⟩
  · intro β J
    rfl
  · intro β
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      exact (Finset.mem_filter.mp (β.property.1 he)).1
    · intro e he
      exact (Finset.mem_filter.mp (β.property.1 he)).2
    · intro e he hfirst
      have hw : TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔ e ∈ β.val := h_branch_trace β e he hfirst
      exact hw
  · intro β β' h_eq
    apply Subtype.ext
    ext e
    constructor
    · intro he
      have h_term : e ∈ terminal := (Finset.mem_filter.mp (β.property.1 he)).1
      have h_first : firstColor e := (Finset.mem_filter.mp (β.property.1 he)).2
      exact (h_eq e h_term h_first).mp he
    · intro he
      have h_term : e ∈ terminal := (Finset.mem_filter.mp (β'.property.1 he)).1
      have h_first : firstColor e := (Finset.mem_filter.mp (β'.property.1 he)).2
      exact (h_eq e h_term h_first).mpr he
  · intro ω h_target h_hist
    rcases htarget_B ω h_target with ⟨B, h_B_supp, h_B_eq⟩
    have h_uR : B.card = uR := (hB_prop B h_B_supp).1
    let A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := (terminal.filter firstColor).filter (fun e => TwoBiteEdgeCoordinateValue ω e)
    have hA_sub : A ⊆ terminal.filter firstColor := Finset.filter_subset _ _
    have hA_prop : ∃ ω', target ω' ∧ ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω' e ↔ e ∈ A) := by
      refine ⟨ω, h_target, ?_⟩
      intro e h_term h_first
      simp [A, h_term, h_first]
    let β_ω : BranchLabel := ⟨A, hA_sub, hA_prop⟩
    
    have h_trace_match : ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) e) := by
      intro e h_term h_first
      have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ redTrace β_ω := by
        simp [redTrace, β_ω, A, h_term, h_first]
      have h2 : TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) e ↔ e ∈ redTrace β_ω := h_branch_trace β_ω e h_term h_first
      rw [h1, h2]

    rcases htarget_branch (branchOfLabel β_ω) ω h_target (h_branch_hist β_ω) (by
      intro e h_term
      rcases e with ⟨_⟩ | ⟨_⟩
      · change TwoBiteEdgeCoordinateValue ω (Sum.inl _) ↔ TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) (Sum.inl _)
        exact h_trace_match (Sum.inl _) h_term trivial
      · trivial) with ⟨J, h_J_eq⟩
    
    have h_blueSupport : blueSupport β_ω J = (TwoBiteStagedOpenPairs ω ε I).filter (fun e => TwoBiteEdgeCoordinateValue ω e ∧ blueColor e) := by
      exact h_J_eq

    let R := blueSupport β_ω J
    have hR_uB : R.card = uB := by
      change (blueSupport β_ω J).card = uB
      rw [h_blueSupport]
      exact htarget_uB ω h_target

    have h_canonical := FixedSetHistoryCellCanonicalAbsenceSelection I hist recorded terminal order R B ω h_hist horder_nodup horder_term (hhist_term ω h_hist) (hhist_pre ω h_hist) (htarget_card ω h_target) (by
      intro e heR
      change e ∈ blueSupport β_ω J at heR
      rw [h_blueSupport] at heR
      have heR_filter := Finset.mem_filter.mp heR
      exact ⟨heR_filter.1, heR_filter.2.1⟩) (by
      intro e heB
      rw [h_B_eq] at heB
      have heB_filter := Finset.mem_filter.mp heB
      exact ⟨heB_filter.1, heB_filter.2.1⟩) (by
      intro e heS heV
      by_cases h_first : firstColor e
      · right
        rw [h_B_eq, Finset.mem_filter]
        exact ⟨heS, heV, h_first⟩
      · left
        change e ∈ blueSupport β_ω J
        rw [h_blueSupport, Finset.mem_filter]
        have h_blue : blueColor e := by
          rcases e with ⟨_⟩ | ⟨_⟩
          · unfold firstColor at h_first
            simp at h_first
          · trivial
        exact ⟨heS, heV, h_blue⟩)

    rcases h_canonical with ⟨Z, hZ_eq, hZ_sub, hZ_disj, hZ_prop, hZ_size⟩
    let blueTerminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      terminal.filter firstColor
    let τ := (terminal.filter (fun e => TwoBiteEdgeCoordinateValue ω e),
      terminal.filter (fun e => ¬ TwoBiteEdgeCoordinateValue ω e), Z)
    have hτ_labels : τ ∈ transcriptLabels := by
      simp only [transcriptLabels, Finset.mem_product, Finset.mem_powerset]
      constructor
      · exact Finset.filter_subset _ _
      · constructor
        · exact Finset.filter_subset _ _
        · exact hZ_sub

    refine ⟨B, h_B_supp, J, β_ω, τ, hτ_labels, ?_⟩
    refine
      ⟨h_target, h_hist, h_B_eq, h_blueSupport, rfl, rfl,
        ?_, ?_,
        h_branch_hist β_ω, rfl, h_branch_trace β_ω, hR_uB, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [R] using hZ_eq
    · intro e he
      exact hZ_prop e he
    · intro e heR
      change e ∈ blueSupport β_ω J at heR
      have heR_filter := Finset.mem_filter.mp (by rw [h_blueSupport] at heR; exact heR)
      exact hhist_term ω h_hist e heR_filter.1
    · intro e heR
      change e ∈ blueSupport β_ω J at heR
      have heR_filter := Finset.mem_filter.mp (by rw [h_blueSupport] at heR; exact heR)
      exact heR_filter.2.2
    · intro e he
      exact (Finset.mem_filter.mp he).1
    · intro e he
      exact (Finset.mem_filter.mp he).1
    · rw [Finset.disjoint_left]
      intro e heP heA
      exact (Finset.mem_filter.mp heA).2 (Finset.mem_filter.mp heP).2
    · intro e he
      rw [Finset.mem_filter]
      constructor
      · rcases Finset.mem_union.mp he with heB | heR
        · exact (hB_prop B h_B_supp).2.1 heB
        · change e ∈ blueSupport β_ω J at heR
          have heR_filter :=
            Finset.mem_filter.mp (by rw [h_blueSupport] at heR; exact heR)
          exact hhist_term ω h_hist e heR_filter.1
      · rcases Finset.mem_union.mp he with heB | heR
        · rw [h_B_eq] at heB
          exact (Finset.mem_filter.mp heB).2.1
        · change e ∈ blueSupport β_ω J at heR
          have heR_filter :=
            Finset.mem_filter.mp (by rw [h_blueSupport] at heR; exact heR)
          exact heR_filter.2.1
    · intro e hterm hfirst
      have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ redTrace β_ω := by
        simp [redTrace, β_ω, A, hterm, hfirst]
      constructor
      · constructor
        · intro heBlue
          exact Finset.mem_filter.mpr ⟨hterm, h1.mpr heBlue⟩
        · intro heP
          exact h1.mp (Finset.mem_filter.mp heP).2
      · constructor
        · intro heNotBlue
          exact
            Finset.mem_filter.mpr
              ⟨hterm, fun hpresent => heNotBlue (h1.mp hpresent)⟩
        · intro heA
          intro heBlue
          exact (Finset.mem_filter.mp heA).2 (h1.mpr heBlue)
    · intro e he
      exact
        Finset.mem_filter.mpr
          ⟨hZ_sub he, (hZ_prop e he).2.1⟩
    · have h_size : max 0 (a - (R.card : ℝ) - (B.card : ℝ)) ≤ (Z.card : ℝ) := by exact_mod_cast hZ_size
      rw [hR_uB] at h_size
      rw [h_uR] at h_size
      exact h_size
    · intro e h_term h_first
      have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ redTrace β_ω := by
        simp [redTrace, β_ω, A, h_term, h_first]
      exact h1
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he
      exact (Finset.mem_filter.mp he).2
  · constructor
    · intro B hB_supp J β τ hτ ω hcell
      rcases hcell with
        ⟨_hTarget, _hHist, _hBlueSupport, _hRedSupport, _hPresentShape,
          _hAbsentShape, _hSelectedShape, _hSelectedPrefix, hBranchHist,
          hRedEq, hBlueBranch, hRcard, hRsub, hRred, hPsub, hAsub, hDisj,
          hMandatory, hBlueTranscript, hZsub, hZlarge, hBlueOmega, hPresent,
          hAbsent⟩
      exact
        ⟨hBranchHist, hRedEq, hBlueBranch, hRcard, hRsub, hRred, hPsub,
          hAsub, hDisj, hMandatory, hBlueTranscript, hZsub, hZlarge,
          hBlueOmega, hPresent, hAbsent⟩
    · constructor
      · intro B hB_supp J β τ hτ ω hcell
        rcases hcell with
          ⟨hTarget, hHist, hBlueSupport, hRedSupport, hPresentShape,
            hAbsentShape, hSelectedShape, hSelectedPrefix, _hBranchHist,
            _hRedEq, _hBlueBranch, _hRcard, _hRsub, _hRred, _hPsub, _hAsub,
            _hDisj, _hMandatory, _hBlueTranscript, _hZsub, _hZlarge,
            _hBlueOmega, _hPresent, _hAbsent⟩
        exact
          ⟨hTarget, hHist, hBlueSupport, hRedSupport, hPresentShape,
            hAbsentShape, hSelectedShape, hSelectedPrefix⟩
      · let cellRealized :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            BlueLabel →
            BranchLabel →
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Prop :=
          fun B J β τ => ∃ ω : TwoBiteSample n m p, cellEvent B J β τ ω
        let assignmentCompatible :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            BlueLabel →
            BranchLabel →
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Prop :=
          fun A _B _J β τ =>
            τ.1 ⊆ A ∧
              Disjoint τ.2.1 A ∧
              (∀ e,
                e ∈ terminal →
                  e ∉ τ.2.2 →
                    firstColor e →
                      (e ∈ redTrace β ↔ e ∈ A)) ∧
              (∀ e,
                e ∈ terminal →
                  firstColor e →
                    (e ∈ redTrace β ↔ e ∈ A))
        refine ⟨cellRealized, assignmentCompatible, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro B hB J β τ hτ hreal
          rcases hreal with ⟨ω, hcell⟩
          have hcell_event : cellEvent B J β τ ω := hcell
          rcases hcell with
            ⟨hTarget, hHist, hBlueSupport, hRedSupport, hPresentShape,
              hAbsentShape, hSelectedShape, hSelectedPrefix, _hBranchHist,
              _hRedEq, _hBlueBranch, _hRcard, _hRsub, _hRred, _hPsub,
              _hAsub, _hDisj, _hMandatory, _hBlueTranscript, _hZsub,
              _hZlarge, _hBlueOmega, _hPresent, _hAbsent⟩
          exact
            ⟨ω, hcell_event, hTarget, hHist, hBlueSupport, hRedSupport,
              hPresentShape, hAbsentShape, hSelectedShape,
              hSelectedPrefix⟩
        · intro B hB J β τ hτ hreal
          rcases hreal with ⟨ω, hcell⟩
          rcases hcell with
            ⟨_hTarget, _hHist, _hBlueSupport, _hRedSupport, _hPresentShape,
              _hAbsentShape, _hSelectedShape, _hSelectedPrefix,
              _hBranchHist, _hRedEq, _hBlueBranch, hRcard, hRsub, hRred,
              hPsub, hAsub, hDisj, hMandatory, hBlueTranscript, hZsub,
              hZlarge, _hBlueOmega, _hPresent, _hAbsent⟩
          exact
            ⟨hRcard, hRsub, hRred, hPsub, hAsub, hDisj, hMandatory,
              hBlueTranscript, hZsub, hZlarge⟩
        · intro B hB J A β τ hA hτ hreal hcompat
          refine ⟨hcompat.1, ?_, hcompat.2.2.1⟩
          rw [Finset.disjoint_left]
          intro e he hA'
          exact
            (Finset.disjoint_left.mp hcompat.2.1
              (Finset.mem_sdiff.mp he).1) hA'
        · intro B hB J A β τ hA hτ hreal hcompat
          exact hcompat.2.2.2
        · intro B hB J A β τ hA hτ hreal hP hDisjoint hBlue
          exact ⟨hP, hDisjoint, (by
            intro e he _heNotSelected hfirst
            exact hBlue e he hfirst), hBlue⟩
        · intro B hB J A β β' τ τ' hA hτ hτ' hreal hreal' hcompat
            hcompat'
          rcases hreal with ⟨ω, hcell⟩
          rcases hreal' with ⟨ω', hcell'⟩
          rcases hcell with
            ⟨_hTarget, hHist, hBlueSupport, hRedSupport, hPresentShape,
              hAbsentShape, hSelectedShape, hSelectedPrefix, _hBranchHist,
              _hRedEq, _hBlueBranch, _hRcard, _hRsub, _hRred, _hPsub,
              _hAsub, _hDisj, _hMandatory, _hBlueTranscript, _hZsub,
              _hZlarge, _hBlueOmega, _hPresent, _hAbsent⟩
          rcases hcell' with
            ⟨_hTarget', hHist', hBlueSupport', hRedSupport',
              hPresentShape', hAbsentShape', hSelectedShape',
              hSelectedPrefix', _hBranchHist', _hRedEq', _hBlueBranch',
              _hRcard', _hRsub', _hRred', _hPsub', _hAsub', _hDisj',
              _hMandatory', _hBlueTranscript', _hZsub', _hZlarge',
              _hBlueOmega', _hPresent', _hAbsent'⟩
          have hblue : ∀ e,
              e ∈ terminal →
                firstColor e →
                  (e ∈ redTrace β ↔ e ∈ redTrace β') := by
            intro e he hfirst
            exact (hcompat.2.2.2 e he hfirst).trans
              (hcompat'.2.2.2 e he hfirst).symm
          have hβ : β = β' := by
            apply Subtype.ext
            ext e
            constructor
            · intro heβ
              have h_term : e ∈ terminal :=
                (Finset.mem_filter.mp (β.property.1 heβ)).1
              have h_first : firstColor e :=
                (Finset.mem_filter.mp (β.property.1 heβ)).2
              exact (hblue e h_term h_first).mp heβ
            · intro heβ'
              have h_term : e ∈ terminal :=
                (Finset.mem_filter.mp (β'.property.1 heβ')).1
              have h_first : firstColor e :=
                (Finset.mem_filter.mp (β'.property.1 heβ')).2
              exact (hblue e h_term h_first).mpr heβ'
          subst β'
          have hA_eq_present : A = τ.1 := by
            ext e
            constructor
            · intro heA
              by_contra hnot
              have hterm : e ∈ terminal := hA heA
              have hnotValue : ¬ TwoBiteEdgeCoordinateValue ω e := by
                intro hvalue
                exact hnot (by
                  rw [hPresentShape]
                  exact Finset.mem_filter.mpr ⟨hterm, hvalue⟩)
              have heAbsent : e ∈ τ.2.1 := by
                rw [hAbsentShape]
                exact Finset.mem_filter.mpr ⟨hterm, hnotValue⟩
              exact (Finset.disjoint_left.mp hcompat.2.1 heAbsent) heA
            · intro heP
              exact hcompat.1 heP
          have hA_eq_present' : A = τ'.1 := by
            ext e
            constructor
            · intro heA
              by_contra hnot
              have hterm : e ∈ terminal := hA heA
              have hnotValue : ¬ TwoBiteEdgeCoordinateValue ω' e := by
                intro hvalue
                exact hnot (by
                  rw [hPresentShape']
                  exact Finset.mem_filter.mpr ⟨hterm, hvalue⟩)
              have heAbsent : e ∈ τ'.2.1 := by
                rw [hAbsentShape']
                exact Finset.mem_filter.mpr ⟨hterm, hnotValue⟩
              exact (Finset.disjoint_left.mp hcompat'.2.1 heAbsent) heA
            · intro heP
              exact hcompat'.1 heP
          have hPresentEq : τ.1 = τ'.1 :=
            hA_eq_present.symm.trans hA_eq_present'
          have hhist_same := hhist_agree ω ω' hHist hHist'
          have hterminal_value_agree :
              ∀ e,
                e ∈ terminal →
                  (TwoBiteEdgeCoordinateValue ω e ↔
                    TwoBiteEdgeCoordinateValue ω' e) := by
            intro e hterm
            have hmem :
                e ∈ τ.1 ↔ e ∈ τ'.1 := by
              rw [hPresentEq]
            have hω :
                TwoBiteEdgeCoordinateValue ω e ↔ e ∈ τ.1 := by
              rw [hPresentShape]
              constructor
              · intro hv
                exact Finset.mem_filter.mpr ⟨hterm, hv⟩
              · intro he
                exact (Finset.mem_filter.mp he).2
            have hω' :
                TwoBiteEdgeCoordinateValue ω' e ↔ e ∈ τ'.1 := by
              rw [hPresentShape']
              constructor
              · intro hv
                exact Finset.mem_filter.mpr ⟨hterm, hv⟩
              · intro he
                exact (Finset.mem_filter.mp he).2
            exact hω.trans (hmem.trans hω'.symm)
          have hAbsentEq : τ.2.1 = τ'.2.1 := by
            rw [hAbsentShape, hAbsentShape']
            ext e
            constructor
            · intro he
              rcases Finset.mem_filter.mp he with ⟨hterm, hnot⟩
              exact Finset.mem_filter.mpr
                ⟨hterm, fun hv' => hnot ((hterminal_value_agree e hterm).mpr hv')⟩
            · intro he
              rcases Finset.mem_filter.mp he with ⟨hterm, hnot⟩
              exact Finset.mem_filter.mpr
                ⟨hterm, fun hv => hnot ((hterminal_value_agree e hterm).mp hv)⟩
          have hSelectedSubset : τ.2.2 ⊆ τ'.2.2 := by
            intro e he
            rcases hSelectedPrefix e he with
              ⟨heStaged, hnotValue, pre, suffix, hsplit, hstable⟩
            have hterm : e ∈ terminal := hhist_term ω hHist e heStaged
            have hpast :
                ∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω c ↔
                      TwoBiteEdgeCoordinateValue ω' c) := by
              intro c hc
              have hcOrder : c ∈ order := by
                have hcList : c ∈ pre := by
                  simpa using hc
                rw [hsplit]
                exact List.mem_append.mpr (Or.inl hcList)
              have hcTerminal : c ∈ terminal := by
                rw [← horder_term]
                simpa using hcOrder
              exact hterminal_value_agree c hcTerminal
            have htests :=
              hstable ω' hhist_same.1 hhist_same.2 hpast
            have heStaged' : e ∈ TwoBiteStagedOpenPairs ω' ε I :=
              htests.1.mp heStaged
            have hnotFixed' : e ∉ blueSupport β J ∪ B := by
              intro hfixed
              have hvalue' : TwoBiteEdgeCoordinateValue ω' e := by
                rcases Finset.mem_union.mp hfixed with heR | heB
                · rw [hRedSupport'] at heR
                  exact (Finset.mem_filter.mp heR).2.1
                · rw [hBlueSupport'] at heB
                  exact (Finset.mem_filter.mp heB).2.1
              exact hnotValue ((hterminal_value_agree e hterm).mpr hvalue')
            rw [hSelectedShape']
            exact Finset.mem_filter.mpr ⟨heStaged', hnotFixed'⟩
          have hSelectedSubset' : τ'.2.2 ⊆ τ.2.2 := by
            intro e he
            rcases hSelectedPrefix' e he with
              ⟨heStaged, hnotValue, pre, suffix, hsplit, hstable⟩
            have hterm : e ∈ terminal := hhist_term ω' hHist' e heStaged
            have hpast :
                ∀ c,
                  c ∈ pre.toFinset →
                    (TwoBiteEdgeCoordinateValue ω' c ↔
                      TwoBiteEdgeCoordinateValue ω c) := by
              intro c hc
              have hcOrder : c ∈ order := by
                have hcList : c ∈ pre := by
                  simpa using hc
                rw [hsplit]
                exact List.mem_append.mpr (Or.inl hcList)
              have hcTerminal : c ∈ terminal := by
                rw [← horder_term]
                simpa using hcOrder
              exact (hterminal_value_agree c hcTerminal).symm
            have hhist_same' := hhist_agree ω' ω hHist' hHist
            have htests :=
              hstable ω hhist_same'.1 hhist_same'.2 hpast
            have heStaged' : e ∈ TwoBiteStagedOpenPairs ω ε I :=
              htests.1.mp heStaged
            have hnotFixed' : e ∉ blueSupport β J ∪ B := by
              intro hfixed
              have hvalue' : TwoBiteEdgeCoordinateValue ω e := by
                rcases Finset.mem_union.mp hfixed with heR | heB
                · rw [hRedSupport] at heR
                  exact (Finset.mem_filter.mp heR).2.1
                · rw [hBlueSupport] at heB
                  exact (Finset.mem_filter.mp heB).2.1
              exact hnotValue ((hterminal_value_agree e hterm).mp hvalue')
            rw [hSelectedShape]
            exact Finset.mem_filter.mpr ⟨heStaged', hnotFixed'⟩
          have hSelectedEq : τ.2.2 = τ'.2.2 :=
            Finset.Subset.antisymm hSelectedSubset hSelectedSubset'
          exact ⟨rfl, Prod.ext hPresentEq (Prod.ext hAbsentEq hSelectedEq)⟩
        · intro B hB J β τ hτ hnot_realized ω hcell
          exact hnot_realized ⟨ω, hcell⟩
