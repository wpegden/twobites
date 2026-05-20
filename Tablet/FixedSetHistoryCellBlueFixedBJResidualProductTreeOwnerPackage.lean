import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.FixedSetHistoryCellBlueFixedBJResidualDecisionTreeSupport
import Tablet.FixedSetHistoryCellBlueFixedBJResidualPartitionData
import Tablet.FixedSetHistoryCellBlueFixedBJResidualReleasedBlockData

-- [TABLET NODE: FixedSetHistoryCellBlueFixedBJResidualProductTreeOwnerPackage]

theorem FixedSetHistoryCellBlueFixedBJResidualProductTreeOwnerPackage :
    ∀ {n m uR uB : ℕ} {p a : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (terminal :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (order : List (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      {BranchLabel : Type} [DecidableEq BranchLabel] [Fintype BranchLabel]
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
          Prop)
      [∀ β : BranchLabel,
        DecidablePred
          (fun τ :
            Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
              Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) =>
            cellRealized β τ)],
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
      ∃ residualOwner :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) →
          Option
            (BranchLabel ×
              (Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) ×
                Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))),
        (∀ β τ,
          τ ∈ transcriptLabels →
            cellRealized β τ →
              ∀ A,
                A ∈ terminal.powerset →
                  (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                    Disjoint (τ.2.1 \ τ.2.2) A →
                      residualOwner A = some (β, τ)) ∧
        (∀ β β' : BranchLabel,
          ∀ τ τ' A,
            τ ∈ transcriptLabels →
              τ' ∈ transcriptLabels →
                cellRealized β τ →
                  cellRealized β' τ' →
                    residualOwner A = some (β, τ) →
                      residualOwner A = some (β', τ') →
                        β = β' ∧ τ = τ') ∧
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
                  (Finset.univ : Finset ResidualLeaf).sum residualLeafMass
                    ≤ 1 ∧
                  (∀ β β' : BranchLabel,
                    ∀ τ τ',
                      τ ∈ transcriptLabels →
                        τ' ∈ transcriptLabels →
                          cellRealized β τ →
                            cellRealized β' τ' →
                              residualLeaf β τ = residualLeaf β' τ' →
                                β = β' ∧ τ = τ') ∧
                  ∀ β τ,
                    τ ∈ transcriptLabels →
                      cellRealized β τ →
                        p ^ (τ.1.card - uB - uR) *
                            ((1 : ℝ) - p) ^ (τ.2.1.card - τ.2.2.card)
                          ≤ residualLeafMass (residualLeaf β τ) := by
-- BODY
  classical
  intro n m uR uB p a hist terminal order B BranchLabel hBranchEq
    hBranchFinite redTrace transcriptLabels BlueLabel hRedFinite J blueSupport
    cellRealized assignmentCompatible hDecReal hp_nonneg hp_half horder_nodup
    horder_terminal hproduct_law hBcard hBterminal hBblue
    hredTrace_functional hrealized_geometry hcompat_forward hcompat_inj
    releasedBlock hreleased_subset hreleased_sound hreleased_complete
    hreleased_disjoint hreleased_cylinder
  letI : DecidableEq BranchLabel := hBranchEq
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let Transcript := Finset Coord × Finset Coord × Finset Coord
  let residualOwner : Finset Coord → Option (BranchLabel × Transcript) :=
    fun A =>
      if h :
          ∃ c : BranchLabel × Transcript,
            c.2 ∈ transcriptLabels ∧
              cellRealized c.1 c.2 ∧ A ∈ releasedBlock c.1 c.2 then
        some (Classical.choose h)
      else
        none
  have howner_cylinder :
      ∀ β τ,
        τ ∈ transcriptLabels →
          cellRealized β τ →
            ∀ A,
              A ∈ terminal.powerset →
                (τ.1 \ (B ∪ blueSupport β J)) ⊆ A →
                  Disjoint (τ.2.1 \ τ.2.2) A →
                    residualOwner A = some (β, τ) := by
    intro β τ hτ hreal A hApow hpresent_res habsent_res
    have hAfilter_mem :
        A ∈ terminal.powerset.filter
          (fun A =>
            (τ.1 \ (B ∪ blueSupport β J)) ⊆ A ∧
              Disjoint (τ.2.1 \ τ.2.2) A) := by
      rw [Finset.mem_filter]
      exact ⟨hApow, hpresent_res, habsent_res⟩
    have hAblock : A ∈ releasedBlock β τ :=
      hreleased_cylinder β τ hτ hreal hAfilter_mem
    have hexists :
        ∃ c : BranchLabel × Transcript,
          c.2 ∈ transcriptLabels ∧
            cellRealized c.1 c.2 ∧ A ∈ releasedBlock c.1 c.2 :=
      ⟨(β, τ), hτ, hreal, hAblock⟩
    dsimp [residualOwner]
    rw [dif_pos hexists]
    let c : BranchLabel × Transcript := Classical.choose hexists
    have hc :
        c.2 ∈ transcriptLabels ∧
          cellRealized c.1 c.2 ∧ A ∈ releasedBlock c.1 c.2 :=
      Classical.choose_spec hexists
    have hsame : c.1 = β ∧ c.2 = τ := by
      by_cases hβ : c.1 = β
      · by_cases hτeq : c.2 = τ
        · exact ⟨hβ, hτeq⟩
        · exact False.elim
            ((hreleased_disjoint c.1 β c.2 τ A hc.1 hτ hc.2.1 hreal
              (Or.inr hτeq) hc.2.2) hAblock)
      · exact False.elim
          ((hreleased_disjoint c.1 β c.2 τ A hc.1 hτ hc.2.1 hreal
            (Or.inl hβ) hc.2.2) hAblock)
    change some c = some (β, τ)
    rcases c with ⟨γ, σ⟩
    rcases hsame with ⟨hγ, hσ⟩
    dsimp at hγ hσ ⊢
    subst γ
    subst σ
    rfl
  have howner_functional :
      ∀ β β' : BranchLabel,
        ∀ τ τ' A,
          τ ∈ transcriptLabels →
            τ' ∈ transcriptLabels →
              cellRealized β τ →
                cellRealized β' τ' →
                  residualOwner A = some (β, τ) →
                    residualOwner A = some (β', τ') →
                      β = β' ∧ τ = τ' := by
    intro β β' τ τ' A _hτ _hτ' _hreal _hreal' howner howner'
    have hpair : (β, τ) = (β', τ') :=
      Option.some.inj (howner.symm.trans howner')
    exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
  obtain
      ⟨assignmentMass, releasedAssignments, releasedCylinderMass,
        hmass_nonneg, hmass_sum, hreleased_subset', hreleased_mass,
        hreleased_disjoint', hreleased_dom⟩ :=
    FixedSetHistoryCellBlueFixedBJResidualPartitionData
      (n := n) (m := m) (uB := uB) (uR := uR) (p := p) (a := a)
      hist terminal order B redTrace transcriptLabels J blueSupport
      cellRealized assignmentCompatible hp_nonneg hp_half horder_nodup
      horder_terminal hproduct_law hBcard hBterminal hBblue
      hredTrace_functional hrealized_geometry hcompat_forward hcompat_inj
      releasedBlock hreleased_subset hreleased_sound hreleased_complete
      hreleased_disjoint hreleased_cylinder
  obtain
      ⟨ResidualLeaf, instResidualLeaf, instResidualLeafEq, residualLeaf,
        residualLeafMass, hleaf_nonneg, hleaf_sum, hleaf_inj, hleaf_dom⟩ :=
    FixedSetHistoryCellBlueFixedBJResidualDecisionTreeSupport
      (n := n) (m := m) (uB := uB) (uR := uR) (p := p) (a := a)
      hist terminal order B redTrace transcriptLabels J blueSupport
      cellRealized assignmentCompatible assignmentMass releasedAssignments
      releasedCylinderMass hp_nonneg hp_half horder_nodup horder_terminal
      hproduct_law hBcard hBterminal hBblue hredTrace_functional
      hrealized_geometry hcompat_forward hcompat_inj hmass_nonneg hmass_sum
      hreleased_subset' hreleased_mass hreleased_disjoint' hreleased_dom
  exact
    ⟨residualOwner, howner_cylinder, howner_functional, ResidualLeaf,
      instResidualLeaf, instResidualLeafEq, residualLeaf, residualLeafMass,
      hleaf_nonneg, hleaf_sum, hleaf_inj, hleaf_dom⟩
