import Tablet.FixedSetHistoryCellRedBranchTranscriptCells
import Tablet.FixedSetHistoryCellRISIResidualScanStability
import Tablet.FixedSetHistoryCellRedFunctionalScanDisjointness

-- [TABLET NODE: FixedSetHistoryCellBlueFixedBJResidualReleasedBlockData]

theorem FixedSetHistoryCellBlueFixedBJResidualReleasedBlockData :
    ∀ {n m uR uB : ℕ} {p ε a : ℝ}
      (I : Finset (Fin n))
      (hist target : TwoBiteSample n m p → Prop)
      (recorded terminal :
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
      (cellEvent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          TwoBiteSample n m p → Prop)
      (cellRealized :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop)
      (assignmentCompatible :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          BlueLabel →
          BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Prop),
      order.Nodup →
      order.toFinset = terminal →
      B ⊆ terminal →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
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
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
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
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  assignmentCompatible A B J β τ →
                    assignmentCompatible A B J β' τ' →
                      β = β' ∧ τ = τ') →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                Disjoint (τ.2.1 \ τ.2.2) A →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ) →
      (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (β β' : BranchLabel)
        (τ τ' :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        A ⊆ terminal →
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  assignmentCompatible
                    ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ →
                    assignmentCompatible
                      ((A \ τ'.2.2) ∪ B ∪ blueSupport β' J) B J β' τ' →
                      β = β' ∧ τ = τ') →
      (∀ (β : BranchLabel)
        (τ :
          Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        τ ∈ transcriptLabels →
          ¬ cellRealized B J β τ →
            ∀ ω : TwoBiteSample n m p,
              ¬ cellEvent B J β τ ω) →
      ∃ releasedBlock :
        BranchLabel →
          (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) →
          Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
        (∀ (β : BranchLabel)
          (τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              releasedBlock β τ ⊆ terminal.powerset) ∧
        (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (β : BranchLabel)
          (τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          A ∈ releasedBlock β τ →
            A ⊆ terminal ∧
              assignmentCompatible
                ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ) ∧
        (∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (β : BranchLabel)
          (τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          A ⊆ terminal →
            τ ∈ transcriptLabels →
              cellRealized B J β τ →
                assignmentCompatible
                  ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ →
                  A ∈ releasedBlock β τ) ∧
        (∀ (β β' : BranchLabel)
          (τ τ' :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
          (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized B J β τ →
                cellRealized B J β' τ' →
                  (β ≠ β' ∨ τ ≠ τ') →
                    A ∈ releasedBlock β τ →
                      A ∉ releasedBlock β' τ') ∧
        ∀ (β : BranchLabel)
          (τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
          τ ∈ transcriptLabels →
            cellRealized B J β τ →
              terminal.powerset.filter
                  (fun A =>
                    (τ.1 \ (B ∪ blueSupport β J)) ⊆ A ∧
                      Disjoint (τ.2.1 \ τ.2.2) A)
                ⊆ releasedBlock β τ := by
-- BODY
  classical
  intro n m uR uB p ε a I hist target recorded terminal order B BranchLabel
    _ redTrace transcriptLabels BlueLabel _ J blueSupport cellEvent
    cellRealized assignmentCompatible horder_nodup horder_terminal hBterminal
    hrealized_geometry hcompat_forward hcompat_inj hresidual_complete
    hresidual_single_owner hnonrealized
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let releasedBlock : BranchLabel → Transcript → Finset (Finset Coord) :=
    fun β τ =>
      terminal.powerset.filter
        (fun A =>
          assignmentCompatible
            ((A \ τ.2.2) ∪ B ∪ blueSupport β J) B J β τ)
  refine ⟨releasedBlock, ?_, ?_, ?_, ?_, ?_⟩
  · intro β τ _hτ _hreal A hA
    exact (Finset.mem_filter.mp hA).1
  · intro A β τ hA
    rw [Finset.mem_filter] at hA
    exact ⟨Finset.mem_powerset.mp hA.1, hA.2⟩
  · intro A β τ hAterminal _hτ _hreal hcompat
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_powerset.mpr hAterminal, hcompat⟩
  · intro β β' τ τ' A hτ hτ' hreal hreal' hdiff hA hA'
    rw [Finset.mem_filter] at hA hA'
    have hAterminal : A ⊆ terminal := Finset.mem_powerset.mp hA.1
    have hsame : β = β' ∧ τ = τ' :=
      hresidual_single_owner A β β' τ τ' hAterminal hτ hτ' hreal
        hreal' hA.2 hA'.2
    rcases hdiff with hβ | hτdiff
    · exact hβ hsame.1
    · exact hτdiff hsame.2
  · intro β τ hτ hreal A hA
    rw [Finset.mem_filter] at hA ⊢
    have hAterminal : A ⊆ terminal := Finset.mem_powerset.mp hA.1
    exact
      ⟨hA.1,
        hresidual_complete A β τ hAterminal hτ hreal hA.2.1 hA.2.2⟩
