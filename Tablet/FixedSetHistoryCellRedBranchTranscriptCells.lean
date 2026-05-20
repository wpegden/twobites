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

-- [TABLET NODE: FixedSetHistoryCellRedBranchTranscriptCells]

theorem FixedSetHistoryCellRedBranchTranscriptCells :
    ∀ {n m uR uB : ℕ} {p ε a : ℝ}
      (I : Finset (Fin n))
      (hist target : TwoBiteSample n m p → Prop)
      (recorded terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (blueSupportLabels :
        Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))))
      {RedLabel : Type} [Fintype RedLabel]
      (branchRedSupport :
        TwoBiteSample n m p →
          RedLabel →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
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
        B ∈ blueSupportLabels →
          B.card = uB ∧
          B ⊆ terminal ∧
          ∀ e,
            e ∈ B →
              match e with
              | Sum.inl _ => False
              | Sum.inr _ => True) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          a ≤ ((TwoBiteStagedOpenPairs ω ε I).card : ℝ)) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          ∃ B,
            B ∈ blueSupportLabels ∧
            B =
              (TwoBiteStagedOpenPairs ω ε I).filter
                (fun e =>
                  TwoBiteEdgeCoordinateValue ω e ∧
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True)) →
      (∀ branch ω : TwoBiteSample n m p,
        target ω →
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
                    | Sum.inr _ => False)) →
      (∀ ω : TwoBiteSample n m p,
        target ω →
          (((TwoBiteStagedOpenPairs ω ε I).filter
            (fun e =>
              TwoBiteEdgeCoordinateValue ω e ∧
                match e with
                | Sum.inl _ => True
                | Sum.inr _ => False)).card = uR)) →
      ∃ (BranchLabel : Type),
        ∃ _ : Fintype BranchLabel,
          ∃ blueTrace :
            BranchLabel →
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            ∃ redSupport :
              BranchLabel →
                RedLabel →
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
                      RedLabel →
                      BranchLabel →
                      (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                      TwoBiteSample n m p → Prop,
            (∀ β : BranchLabel, hist (branchOfLabel β)) ∧
            (∀ (β : BranchLabel) (J : RedLabel),
              redSupport β J =
                branchRedSupport (branchOfLabel β) J) ∧
            (∀ β : BranchLabel,
              blueTrace β ⊆ terminal ∧
                (∀ e,
                  e ∈ blueTrace β →
                    match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) ∧
                (∀ e,
                  e ∈ terminal →
                    (match e with
                    | Sum.inl _ => False
                    | Sum.inr _ => True) →
                      (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔
                        e ∈ blueTrace β))) ∧
            (∀ β β' : BranchLabel,
              (∀ e,
                e ∈ terminal →
                  (match e with
                  | Sum.inl _ => False
                  | Sum.inr _ => True) →
                    (e ∈ blueTrace β ↔ e ∈ blueTrace β')) →
                β = β') ∧
            (∀ ω : TwoBiteSample n m p,
              target ω →
                hist ω →
                  ∃ B,
                    B ∈ blueSupportLabels ∧
                      ∃ J : RedLabel,
                        ∃ β,
                          ∃ τ,
                            τ ∈ transcriptLabels ∧
                              cellEvent B J β τ ω) ∧
            (∀ B,
              B ∈ blueSupportLabels →
                ∀ J : RedLabel,
                  ∀ β,
                    ∀ τ,
                      τ ∈ transcriptLabels →
                        ∀ ω : TwoBiteSample n m p,
                          cellEvent B J β τ ω →
                            hist (branchOfLabel β) ∧
                            redSupport β J =
                              branchRedSupport (branchOfLabel β) J ∧
                            (∀ e,
                              e ∈ terminal →
                                (match e with
                                | Sum.inl _ => False
                                | Sum.inr _ => True) →
                                  (TwoBiteEdgeCoordinateValue
                                    (branchOfLabel β) e ↔
                                      e ∈ blueTrace β)) ∧
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
                                ¬ TwoBiteEdgeCoordinateValue ω e)) ∧
            ∃ cellRealized :
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                RedLabel →
                BranchLabel →
                (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                Prop,
              ∃ assignmentCompatible :
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                  Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
                  RedLabel →
                  BranchLabel →
                  (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                    Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
                  Prop,
                (∀ B,
                  B ∈ blueSupportLabels →
                    ∀ J : RedLabel,
                      ∀ β,
                        ∀ τ,
                          τ ∈ transcriptLabels →
                            cellRealized B J β τ →
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
                                ≤ ((τ.2.2).card : ℝ)) ∧
                (∀ B,
                  B ∈ blueSupportLabels →
                    ∀ J : RedLabel,
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
                                      | Sum.inl _ => False
                                      | Sum.inr _ => True) →
                                        (e ∈ blueTrace β ↔ e ∈ A)) ∧
                (∀ B,
                  B ∈ blueSupportLabels →
                    ∀ J : RedLabel,
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
                          B ∈ blueSupportLabels →
                            ∀ J : RedLabel,
                              ∀ β,
                        ∀ τ,
                          τ ∈ transcriptLabels →
                            ¬ cellRealized B J β τ →
                              ∀ ω : TwoBiteSample n m p,
                                ¬ cellEvent B J β τ ω) := by
-- BODY
  intros n m uR uB p ε a I hist target recorded terminal order blueSupportLabels RedLabel _ branchRedSupport
  intros _ _ _hp_nonneg _hp_half horder_nodup horder_term hterminal_not_recorded hrecorded_universe hterminal_universe htarget_hist hhist_term hhist_pre hB_prop htarget_card htarget_B htarget_branch htarget_uR

  let firstColor (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
    match e with | Sum.inl _ => False | Sum.inr _ => True
  let redColor (e : Sum (Fin m × Fin m) (Fin m × Fin m)) : Prop :=
    match e with | Sum.inl _ => True | Sum.inr _ => False
  
  let BranchLabel := { A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) //
    A ⊆ terminal.filter firstColor ∧ ∃ ω, target ω ∧ ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A) }
  
  have instBranchLabel : Fintype BranchLabel := Fintype.ofFinite BranchLabel
  
  let blueTrace (β : BranchLabel) : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := β.val
  
  let branchOfLabel (β : BranchLabel) : TwoBiteSample n m p :=
    Classical.choose β.property.2
    
  have h_branch_target (β : BranchLabel) : target (branchOfLabel β) :=
    (Classical.choose_spec β.property.2).1

  have h_branch_hist (β : BranchLabel) : hist (branchOfLabel β) :=
    htarget_hist _ (h_branch_target β)
    
  have h_branch_trace (β : BranchLabel) : ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔ e ∈ β.val) :=
    (Classical.choose_spec β.property.2).2

  let redSupport (β : BranchLabel) (J : RedLabel) : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    branchRedSupport (branchOfLabel β) J

  let transcriptLabels : Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) :=
    (Finset.powerset terminal) ×ˢ (Finset.powerset terminal) ×ˢ (Finset.powerset terminal)

  let cellEvent (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) (J : RedLabel) (β : BranchLabel) 
      (τ : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) × Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) 
      (ω : TwoBiteSample n m p) : Prop :=
    hist (branchOfLabel β) ∧
    redSupport β J = branchRedSupport (branchOfLabel β) J ∧
    (∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue (branchOfLabel β) e ↔ e ∈ blueTrace β)) ∧
    (redSupport β J).card = uR ∧
    redSupport β J ⊆ terminal ∧
    (∀ e ∈ redSupport β J, redColor e) ∧
    τ.1 ⊆ terminal ∧
    τ.2.1 ⊆ terminal ∧
    Disjoint τ.1 τ.2.1 ∧
    B ∪ redSupport β J ⊆ τ.1 ∧
    (∀ e ∈ terminal, firstColor e →
      (e ∈ blueTrace β ↔ e ∈ τ.1) ∧
      (e ∉ blueTrace β ↔ e ∈ τ.2.1)) ∧
    τ.2.2 ⊆ τ.2.1 ∧
    max 0 (a - (uR : ℝ) - (uB : ℝ)) ≤ ((τ.2.2).card : ℝ) ∧
    (∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β)) ∧
    (∀ e ∈ τ.1, TwoBiteEdgeCoordinateValue ω e) ∧
    (∀ e ∈ τ.2.1, ¬ TwoBiteEdgeCoordinateValue ω e)

  refine ⟨BranchLabel, instBranchLabel, blueTrace, redSupport, branchOfLabel, transcriptLabels, cellEvent, 
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
    have h_uB : B.card = uB := (hB_prop B h_B_supp).1
    let A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) := (terminal.filter firstColor).filter (fun e => TwoBiteEdgeCoordinateValue ω e)
    have hA_sub : A ⊆ terminal.filter firstColor := Finset.filter_subset _ _
    have hA_prop : ∃ ω', target ω' ∧ ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω' e ↔ e ∈ A) := by
      refine ⟨ω, h_target, ?_⟩
      intro e h_term h_first
      simp [A, h_term, h_first]
    let β_ω : BranchLabel := ⟨A, hA_sub, hA_prop⟩
    
    have h_trace_match : ∀ e ∈ terminal, firstColor e → (TwoBiteEdgeCoordinateValue ω e ↔ TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) e) := by
      intro e h_term h_first
      have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
        simp [blueTrace, β_ω, A, h_term, h_first]
      have h2 : TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) e ↔ e ∈ blueTrace β_ω := h_branch_trace β_ω e h_term h_first
      rw [h1, h2]

    rcases htarget_branch (branchOfLabel β_ω) ω h_target (h_branch_hist β_ω) (by
      intro e h_term
      rcases e with ⟨_⟩ | ⟨_⟩
      · trivial
      · change TwoBiteEdgeCoordinateValue ω (Sum.inr _) ↔ TwoBiteEdgeCoordinateValue (branchOfLabel β_ω) (Sum.inr _)
        exact h_trace_match (Sum.inr _) h_term trivial) with ⟨J, h_J_eq⟩
    
    have h_redSupport : redSupport β_ω J = (TwoBiteStagedOpenPairs ω ε I).filter (fun e => TwoBiteEdgeCoordinateValue ω e ∧ redColor e) := by
      exact h_J_eq

    let R := redSupport β_ω J
    have hR_uR : R.card = uR := by
      change (redSupport β_ω J).card = uR
      rw [h_redSupport]
      exact htarget_uR ω h_target

    have h_canonical := FixedSetHistoryCellCanonicalAbsenceSelection I hist recorded terminal order R B ω h_hist horder_nodup horder_term (hhist_term ω h_hist) (hhist_pre ω h_hist) (htarget_card ω h_target) (by
      intro e heR
      change e ∈ redSupport β_ω J at heR
      rw [h_redSupport] at heR
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
        change e ∈ redSupport β_ω J
        rw [h_redSupport, Finset.mem_filter]
        have h_red : redColor e := by
          rcases e with ⟨_⟩ | ⟨_⟩
          · trivial
          · unfold firstColor at h_first
            simp at h_first
        exact ⟨heS, heV, h_red⟩)

    rcases h_canonical with ⟨Z, hZ_sub, hZ_disj, hZ_prop, hZ_size⟩
    let blueTerminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      terminal.filter firstColor
    let τ := (B ∪ R ∪ blueTrace β_ω,
      Z ∪ (blueTerminal \ blueTrace β_ω), Z)
    have hτ_labels : τ ∈ transcriptLabels := by
      simp only [transcriptLabels, Finset.mem_product, Finset.mem_powerset]
      constructor
      · intro e he
        rcases Finset.mem_union.mp he with heBR | heBlue
        · rcases Finset.mem_union.mp heBR with heB | heR
          · exact (hB_prop B h_B_supp).2.1 heB
          · change e ∈ redSupport β_ω J at heR
            have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
            exact hhist_term ω h_hist e heR_filter.1
        · exact (Finset.mem_filter.mp (β_ω.property.1 heBlue)).1
      · constructor
        · intro e he
          rcases Finset.mem_union.mp he with heZ | heBlue
          · exact hZ_sub heZ
          · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp heBlue).1).1
        · exact hZ_sub

    refine ⟨B, h_B_supp, J, β_ω, τ, hτ_labels, ?_⟩
    refine ⟨h_branch_hist β_ω, rfl, h_branch_trace β_ω, hR_uR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e heR
      change e ∈ redSupport β_ω J at heR
      have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
      exact hhist_term ω h_hist e heR_filter.1
    · intro e heR
      change e ∈ redSupport β_ω J at heR
      have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
      exact heR_filter.2.2
    · intro e he
      rcases Finset.mem_union.mp he with heBR | heBlue
      · rcases Finset.mem_union.mp heBR with heB | heR
        · exact (hB_prop B h_B_supp).2.1 heB
        · change e ∈ redSupport β_ω J at heR
          have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
          exact hhist_term ω h_hist e heR_filter.1
      · exact (Finset.mem_filter.mp (β_ω.property.1 heBlue)).1
    · intro e he
      rcases Finset.mem_union.mp he with heZ | heBlue
      · exact hZ_sub heZ
      · exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp heBlue).1).1
    · rw [Finset.disjoint_left]
      intro e heP heA
      rcases Finset.mem_union.mp heA with heZ | heBlueAbsent
      · rcases Finset.mem_union.mp heP with heBR | heBlue
        · have heRB : e ∈ R ∪ B := by
            rcases Finset.mem_union.mp heBR with heB | heR
            · exact Finset.mem_union.mpr (Or.inr heB)
            · exact Finset.mem_union.mpr (Or.inl heR)
          exact (Finset.disjoint_left.mp hZ_disj heZ) heRB
        · have hterm : e ∈ terminal :=
            (Finset.mem_filter.mp (β_ω.property.1 heBlue)).1
          have hfirst : firstColor e :=
            (Finset.mem_filter.mp (β_ω.property.1 heBlue)).2
          have hpresent : TwoBiteEdgeCoordinateValue ω e := by
            have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
              simp [blueTrace, β_ω, A, hterm, hfirst]
            exact h1.mpr heBlue
          exact (hZ_prop e heZ).2.1 hpresent
      · rcases Finset.mem_sdiff.mp heBlueAbsent with ⟨heBlueTerm, heNotBlue⟩
        rcases Finset.mem_union.mp heP with heBR | heBlue
        · rcases Finset.mem_union.mp heBR with heB | heR
          · have hterm : e ∈ terminal := (hB_prop B h_B_supp).2.1 heB
            have hfirst : firstColor e := (hB_prop B h_B_supp).2.2 e heB
            have hpresent : TwoBiteEdgeCoordinateValue ω e := by
              rw [h_B_eq] at heB
              exact (Finset.mem_filter.mp heB).2.1
            have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
              simp [blueTrace, β_ω, A, hterm, hfirst]
            exact heNotBlue (h1.mp hpresent)
          · have hred : redColor e := by
              change e ∈ redSupport β_ω J at heR
              have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
              exact heR_filter.2.2
            have hfirst : firstColor e := (Finset.mem_filter.mp heBlueTerm).2
            rcases e with ⟨_⟩ | ⟨_⟩
            · exact hfirst
            · exact hred
        · exact heNotBlue heBlue
    · intro e he
      exact Finset.mem_union.mpr (Or.inl he)
    · intro e hterm hfirst
      constructor
      · constructor
        · intro heBlue
          exact Finset.mem_union.mpr (Or.inr heBlue)
        · intro heP
          rcases Finset.mem_union.mp heP with heBR | heBlue
          · rcases Finset.mem_union.mp heBR with heB | heR
            · have hpresent : TwoBiteEdgeCoordinateValue ω e := by
                rw [h_B_eq] at heB
                exact (Finset.mem_filter.mp heB).2.1
              have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
                simp [blueTrace, β_ω, A, hterm, hfirst]
              exact h1.mp hpresent
            · have hred : redColor e := by
                change e ∈ redSupport β_ω J at heR
                have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
                exact heR_filter.2.2
              rcases e with ⟨_⟩ | ⟨_⟩
              · exact hfirst.elim
              · exact hred.elim
          · exact heBlue
      · constructor
        · intro heNotBlue
          exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_sdiff.mpr ⟨by simp [blueTerminal, hterm, hfirst], heNotBlue⟩))
        · intro heA
          rcases Finset.mem_union.mp heA with heZ | heBlueAbsent
          · intro heBlue
            have hpresent : TwoBiteEdgeCoordinateValue ω e := by
              have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
                simp [blueTrace, β_ω, A, hterm, hfirst]
              exact h1.mpr heBlue
            exact (hZ_prop e heZ).2.1 hpresent
          · exact (Finset.mem_sdiff.mp heBlueAbsent).2
    · intro e he
      exact Finset.mem_union.mpr (Or.inl he)
    · have h_size : max 0 (a - (R.card : ℝ) - (B.card : ℝ)) ≤ (Z.card : ℝ) := by exact_mod_cast hZ_size
      rw [hR_uR] at h_size
      rw [h_uB] at h_size
      exact h_size
    · intro e h_term h_first
      have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
        simp [blueTrace, β_ω, A, h_term, h_first]
      exact h1
    · intro e he
      rcases Finset.mem_union.mp he with heBR | heBlue
      · rcases Finset.mem_union.mp heBR with heB | heR
        · rw [h_B_eq] at heB
          exact (Finset.mem_filter.mp heB).2.1
        · change e ∈ redSupport β_ω J at heR
          have heR_filter := Finset.mem_filter.mp (by rw [h_redSupport] at heR; exact heR)
          exact heR_filter.2.1
      · have hterm : e ∈ terminal :=
          (Finset.mem_filter.mp (β_ω.property.1 heBlue)).1
        have hfirst : firstColor e :=
          (Finset.mem_filter.mp (β_ω.property.1 heBlue)).2
        have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
          simp [blueTrace, β_ω, A, hterm, hfirst]
        exact h1.mpr heBlue
    · intro e he
      rcases Finset.mem_union.mp he with heZ | heBlueAbsent
      · exact (hZ_prop e heZ).2.1
      · rcases Finset.mem_sdiff.mp heBlueAbsent with ⟨heBlueTerm, heNotBlue⟩
        have hterm : e ∈ terminal := (Finset.mem_filter.mp heBlueTerm).1
        have hfirst : firstColor e := (Finset.mem_filter.mp heBlueTerm).2
        have h1 : TwoBiteEdgeCoordinateValue ω e ↔ e ∈ blueTrace β_ω := by
          simp [blueTrace, β_ω, A, hterm, hfirst]
        exact fun hpresent => heNotBlue (h1.mp hpresent)
  · constructor
    · intro B hB_supp J β τ hτ ω hcell
      exact hcell
    · let cellRealized :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            RedLabel →
            BranchLabel →
            (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
            Prop :=
          fun B J β τ => ∃ ω : TwoBiteSample n m p, cellEvent B J β τ ω
      let assignmentCompatible :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
            RedLabel →
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
                      (e ∈ blueTrace β ↔ e ∈ A)) ∧
              (∀ e,
                e ∈ terminal →
                  firstColor e →
                    (e ∈ blueTrace β ↔ e ∈ A)) ∧
              ∀ β' τ',
                τ' ∈ transcriptLabels →
                  cellRealized _B _J β' τ' →
                  τ'.1 ⊆ A →
                  Disjoint τ'.2.1 A →
                  (∀ e,
                    e ∈ terminal →
                      firstColor e →
                        (e ∈ blueTrace β' ↔ e ∈ A)) →
                    τ' = τ
      refine ⟨cellRealized, assignmentCompatible, ?_, ?_, ?_, ?_⟩
      · intro B hB J β τ hτ hreal
        rcases hreal with ⟨ω, hcell⟩
        rcases hcell with
          ⟨_hBranchHist, _hRedEq, _hBlueBranch, hRcard, hRsub, hRred,
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
      · intro B hB J A β β' τ τ' hA hτ hτ' hreal hreal' hcompat
          hcompat'
        have hblue : ∀ e,
            e ∈ terminal →
              firstColor e →
                (e ∈ blueTrace β ↔ e ∈ blueTrace β') := by
          intro e he hfirst
          exact (hcompat.2.2.2.1 e he hfirst).trans
            (hcompat'.2.2.2.1 e he hfirst).symm
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
        have hτ' : τ' = τ :=
          hcompat.2.2.2.2 β' τ' hτ' hreal' hcompat'.1
            hcompat'.2.1 hcompat'.2.2.2.1
        exact ⟨hβ, hτ'.symm⟩
      · intro B hB J β τ hτ hnot_realized ω hcell
        exact hnot_realized ⟨ω, hcell⟩
