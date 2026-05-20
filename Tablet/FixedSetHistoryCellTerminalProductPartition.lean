import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellTerminalProductPartition]

theorem FixedSetHistoryCellTerminalProductPartition :
    ∀ {n m : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
        (terminal : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
        (E : TwoBiteSample n m p → Prop)
        (W : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → Prop)
        [∀ (ω : TwoBiteSample n m p)
          (e : Sum (Fin m × Fin m) (Fin m × Fin m)),
          Decidable (TwoBiteEdgeCoordinateValue ω e)]
        [DecidablePred W],
      (∀ ω : TwoBiteSample n m p,
        hist ω →
          (E ω ↔
            W (terminal.filter
              (fun e => TwoBiteEdgeCoordinateValue ω e)))) →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      TwoBiteConditionalProbability n m p E hist
        ≤
        (terminal.powerset.filter W).sum
            (fun A =>
              p ^ A.card *
                ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
-- BODY
  intro n m p hist terminal E W _ _ hdet hproduct
  classical
  let Ω := TwoBiteSample n m p
  let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
  let prob : (Ω → Prop) → ℝ := fun F => TwoBiteEventProbability n m p F
  let present : Ω → Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    fun ω => terminal.filter (fun e => TwoBiteEdgeCoordinateValue ω e)
  let cell :
      Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) → Ω → Prop :=
    fun A ω =>
      ∀ e, e ∈ terminal → (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)
  let selected :
      Finset (Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) :=
    terminal.powerset.filter W
  have hpresent_subset :
      ∀ ω : Ω, present ω ⊆ terminal := by
    intro ω e he
    exact (Finset.mem_filter.mp he).1
  have hselected_subset :
      ∀ A, A ∈ selected → A ⊆ terminal := by
    intro A hA
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hselected_W :
      ∀ A, A ∈ selected → W A := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2
  have hcell_iff_present :
      ∀ (A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))) (ω : Ω),
        A ⊆ terminal → (cell A ω ↔ present ω = A) := by
    intro A ω hA
    constructor
    · intro hcell
      ext e
      constructor
      · intro he
        exact (hcell e (Finset.mem_filter.mp he).1).1
          (Finset.mem_filter.mp he).2
      · intro he
        have hterm : e ∈ terminal := hA he
        have hedge : TwoBiteEdgeCoordinateValue ω e := (hcell e hterm).2 he
        exact Finset.mem_filter.mpr ⟨hterm, hedge⟩
    · intro hEq e hterm
      constructor
      · intro hedge
        have he_present : e ∈ present ω :=
          Finset.mem_filter.mpr ⟨hterm, hedge⟩
        simpa [hEq] using he_present
      · intro heA
        have he_present : e ∈ present ω := by
          simpa [hEq] using heA
        exact (Finset.mem_filter.mp he_present).2
  have hcell_present :
      ∀ ω : Ω, cell (present ω) ω := by
    intro ω e hterm
    constructor
    · intro hedge
      exact Finset.mem_filter.mpr ⟨hterm, hedge⟩
    · intro he
      exact (Finset.mem_filter.mp he).2
  have prob_eq_sum_if :
      ∀ F : Ω → Prop,
        prob F = (Finset.univ : Finset Ω).sum
          (fun ω => if F ω then w ω else 0) := by
    intro F
    unfold prob TwoBiteEventProbability
    rw [Finset.sum_filter]
  have hnum_eq_sum :
      prob (fun ω : Ω => E ω ∧ hist ω) =
        selected.sum (fun A => prob (fun ω : Ω => cell A ω ∧ hist ω)) := by
    rw [prob_eq_sum_if]
    trans
        (Finset.univ : Finset Ω).sum
          (fun ω =>
            selected.sum
              (fun A => if cell A ω ∧ hist ω then w ω else 0))
    · refine Finset.sum_congr rfl ?_
      intro ω hω
      by_cases hhist : hist ω
      · by_cases hE : E ω
        · let A0 := present ω
          have hA0_mem : A0 ∈ selected := by
            have hW0 : W A0 := (hdet ω hhist).mp hE
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_powerset.mpr (hpresent_subset ω), hW0⟩
          have hsum_single :
              selected.sum
                  (fun A => if cell A ω ∧ hist ω then w ω else 0)
                =
              (if cell A0 ω ∧ hist ω then w ω else 0) := by
            refine Finset.sum_eq_single A0 ?_ ?_
            · intro B hB hBA
              have hnot_cell : ¬ cell B ω := by
                intro hcellB
                have hEq : present ω = B :=
                  (hcell_iff_present B ω (hselected_subset B hB)).1 hcellB
                exact hBA (by simpa [A0] using hEq.symm)
              simp [hnot_cell]
            · intro hA0_not_mem
              exact False.elim (hA0_not_mem hA0_mem)
          have hcellA0 : cell A0 ω := by
            simpa [A0] using hcell_present ω
          rw [hsum_single]
          simp [hE, hhist, hcellA0]
        · have hsum_zero :
              selected.sum
                  (fun A => if cell A ω ∧ hist ω then w ω else 0)
                = 0 := by
            refine Finset.sum_eq_zero ?_
            intro A hA
            have hnot : ¬ (cell A ω ∧ hist ω) := by
              intro hcell_hist
              have hEq : present ω = A :=
                (hcell_iff_present A ω (hselected_subset A hA)).1
                  hcell_hist.1
              have hW_present : W (present ω) := by
                simpa [hEq] using hselected_W A hA
              exact hE ((hdet ω hhist).mpr hW_present)
            simp [hnot]
          rw [hsum_zero]
          simp [hE]
      · have hsum_zero :
            selected.sum
                (fun A => if cell A ω ∧ hist ω then w ω else 0)
              = 0 := by
          refine Finset.sum_eq_zero ?_
          intro A hA
          simp [hhist]
        rw [hsum_zero]
        simp [hhist]
    · calc
        (Finset.univ : Finset Ω).sum
            (fun ω =>
              selected.sum
                (fun A => if cell A ω ∧ hist ω then w ω else 0))
            =
          selected.sum
            (fun A =>
              (Finset.univ : Finset Ω).sum
                (fun ω => if cell A ω ∧ hist ω then w ω else 0)) := by
              rw [Finset.sum_comm]
      _ =
          selected.sum
            (fun A => prob (fun ω : Ω => cell A ω ∧ hist ω)) := by
              refine Finset.sum_congr rfl ?_
              intro A hA
              symm
              unfold prob TwoBiteEventProbability
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro ω hω
              by_cases h : cell A ω ∧ hist ω <;> simp [h, w]
  by_cases hden : prob hist = 0
  · have hleft :
        TwoBiteConditionalProbability n m p E hist = 0 := by
      simp [TwoBiteConditionalProbability, prob, hden]
    have hterm_zero :
        selected.sum
            (fun A =>
              p ^ A.card *
                ((1 : ℝ) - p) ^ (terminal.card - A.card))
          = 0 := by
      refine Finset.sum_eq_zero ?_
      intro A hA
      have hcond_zero :
          TwoBiteConditionalProbability n m p (cell A) hist = 0 := by
        simp [TwoBiteConditionalProbability, prob, hden]
      have hprod := hproduct A (hselected_subset A hA)
      rw [← hprod]
      exact hcond_zero
    rw [hleft, hterm_zero]
  · have hcond_eq_sum :
        TwoBiteConditionalProbability n m p E hist =
          selected.sum
            (fun A => TwoBiteConditionalProbability n m p (cell A) hist) := by
      have hden' : TwoBiteEventProbability n m p hist ≠ 0 := by
        simpa [prob] using hden
      calc
        TwoBiteConditionalProbability n m p E hist
            =
            prob (fun ω : Ω => E ω ∧ hist ω) / prob hist := by
              unfold TwoBiteConditionalProbability
              rw [if_neg hden']
        _ =
          (selected.sum
              (fun A => prob (fun ω : Ω => cell A ω ∧ hist ω))) /
            prob hist := by
              rw [hnum_eq_sum]
        _ =
          selected.sum
            (fun A => prob (fun ω : Ω => cell A ω ∧ hist ω) / prob hist) := by
              simp [div_eq_mul_inv, Finset.sum_mul]
        _ =
            selected.sum
              (fun A =>
                TwoBiteConditionalProbability n m p (cell A) hist) := by
                refine Finset.sum_congr rfl ?_
                intro A hA
                unfold TwoBiteConditionalProbability
                rw [if_neg hden']
    calc
      TwoBiteConditionalProbability n m p E hist
          =
        selected.sum
          (fun A => TwoBiteConditionalProbability n m p (cell A) hist) := hcond_eq_sum
      _ =
        selected.sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
          refine Finset.sum_congr rfl ?_
          intro A hA
          exact hproduct A (hselected_subset A hA)
      _ ≤
        selected.sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) := le_rfl
