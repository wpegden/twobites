import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellAdaptiveBranchPartition]

theorem FixedSetHistoryCellAdaptiveBranchPartition :
    ∀ {n m : ℕ} {p : ℝ}
        (hist fixedCount : TwoBiteSample n m p → Prop)
        (terminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (firstColor : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop)
        [DecidablePred firstColor],
      (∀ ω : TwoBiteSample n m p, fixedCount ω → hist ω) →
      (∀ ω : TwoBiteSample n m p,
        hist ω → fixedCount ω →
          ∃ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            A ⊆ terminal.filter firstColor ∧
              ∀ e, e ∈ terminal → firstColor e →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) →
      (∀ ω : TwoBiteSample n m p,
        hist ω → fixedCount ω →
          ∃ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
            A ⊆ terminal.filter firstColor ∧
              (hist ω ∧
                ∀ e, e ∈ terminal → firstColor e →
                  (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))) ∧
        (∀ A B : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
          A ⊆ terminal.filter firstColor →
          B ⊆ terminal.filter firstColor →
          A ≠ B →
            ∀ ω : TwoBiteSample n m p,
              ¬
                ((hist ω ∧
                    ∀ e, e ∈ terminal → firstColor e →
                      (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
                  (hist ω ∧
                      ∀ e, e ∈ terminal → firstColor e →
                        (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ B)))) := by
-- BODY
  intro n m p hist fixedCount terminal firstColor _ hfixed_hist htrace
  constructor
  · intro ω hhist hfixed
    rcases htrace ω hhist hfixed with ⟨A, hA_sub, hA_trace⟩
    exact ⟨A, hA_sub, hhist, hA_trace⟩
  · intro A B hA_sub hB_sub hAB ω hboth
    rcases hboth with ⟨⟨_, hA_trace⟩, ⟨_, hB_trace⟩⟩
    apply hAB
    ext e
    constructor
    · intro heA
      have heA_filter : e ∈ terminal.filter firstColor := hA_sub heA
      have hterm : e ∈ terminal := (Finset.mem_filter.mp heA_filter).1
      have hfirst : firstColor e := (Finset.mem_filter.mp heA_filter).2
      have hvalue : TwoBiteEdgeCoordinateValue ω e :=
        (hA_trace e hterm hfirst).2 heA
      exact (hB_trace e hterm hfirst).1 hvalue
    · intro heB
      have heB_filter : e ∈ terminal.filter firstColor := hB_sub heB
      have hterm : e ∈ terminal := (Finset.mem_filter.mp heB_filter).1
      have hfirst : firstColor e := (Finset.mem_filter.mp heB_filter).2
      have hvalue : TwoBiteEdgeCoordinateValue ω e :=
        (hB_trace e hterm hfirst).2 heB
      exact (hA_trace e hterm hfirst).1 hvalue
