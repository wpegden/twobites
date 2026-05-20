import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Ring
import Tablet.FixedSetHistoryCellTerminalProductPartition
import Tablet.TwoBiteConditionalProbability
import Tablet.TwoBiteEdgeCoordinateValue

-- [TABLET NODE: FixedSetHistoryCellFixedCylinderCharge]

theorem FixedSetHistoryCellFixedCylinderCharge :
    ∀ {n m : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (terminal present absent :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      0 ≤ p →
      p ≤ 1 →
      present ⊆ terminal →
      absent ⊆ terminal →
      Disjoint present absent →
      (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ terminal →
          TwoBiteConditionalProbability n m p
            (fun ω =>
              ∀ e, e ∈ terminal →
                (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A))
            hist =
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) →
      TwoBiteConditionalProbability n m p
          (fun ω =>
            (∀ e, e ∈ present → TwoBiteEdgeCoordinateValue ω e) ∧
              (∀ e, e ∈ absent → ¬ TwoBiteEdgeCoordinateValue ω e))
          hist
        ≤
        p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
-- BODY
  classical
  intro n m p hist terminal present absent hp0 hp1 hpresent habsent hdisj hproduct
  let Ω := TwoBiteSample n m p
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let cylinder : Ω → Prop := fun ω =>
    (∀ e, e ∈ present → TwoBiteEdgeCoordinateValue ω e) ∧
      (∀ e, e ∈ absent → ¬ TwoBiteEdgeCoordinateValue ω e)
  let W : Finset Coord → Prop := fun A => present ⊆ A ∧ Disjoint A absent
  have hdet :
      ∀ ω : Ω,
        hist ω →
          (cylinder ω ↔
            W (terminal.filter
              (fun e => TwoBiteEdgeCoordinateValue ω e))) := by
    intro ω hhist
    constructor
    · intro hcyl
      constructor
      · intro e he_present
        exact Finset.mem_filter.mpr
          ⟨hpresent he_present, hcyl.1 e he_present⟩
      · refine Finset.disjoint_left.mpr ?_
        intro e he_filter he_absent
        have hedge : TwoBiteEdgeCoordinateValue ω e :=
          (Finset.mem_filter.mp he_filter).2
        exact hcyl.2 e he_absent hedge
    · intro hW
      constructor
      · intro e he_present
        have he_filter : e ∈ terminal.filter
            (fun e => TwoBiteEdgeCoordinateValue ω e) :=
          hW.1 he_present
        exact (Finset.mem_filter.mp he_filter).2
      · intro e he_absent hedge
        have he_filter : e ∈ terminal.filter
            (fun e => TwoBiteEdgeCoordinateValue ω e) :=
          Finset.mem_filter.mpr ⟨habsent he_absent, hedge⟩
        exact (Finset.disjoint_left.mp hW.2 he_filter) he_absent
  have hpartition :
      TwoBiteConditionalProbability n m p cylinder hist
        ≤
        (terminal.powerset.filter W).sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
    exact FixedSetHistoryCellTerminalProductPartition
      (n := n) (m := m) (p := p) hist terminal cylinder W hdet hproduct
  let upper : Finset Coord := terminal \ absent
  let free : Finset Coord := upper \ present
  have hpresent_upper : present ⊆ upper := by
    exact (Finset.subset_sdiff).2 ⟨hpresent, hdisj⟩
  have hselected_eq :
      terminal.powerset.filter W = Finset.Icc present upper := by
    ext A
    simp [W, upper, Finset.Icc_eq_filter_powerset, Finset.subset_sdiff,
      and_assoc, and_left_comm, and_comm]
  have himage_inj :
      Set.InjOn (fun V : Finset Coord => present ∪ V) (free.powerset : Set (Finset Coord)) := by
    intro V hV V' hV' hEq
    have hV_subset : V ⊆ free := Finset.mem_powerset.mp hV
    have hV'_subset : V' ⊆ free := Finset.mem_powerset.mp hV'
    have hV_disj : Disjoint present V :=
      disjoint_sdiff_self_right.mono_right hV_subset
    have hV'_disj : Disjoint present V' :=
      disjoint_sdiff_self_right.mono_right hV'_subset
    ext e
    constructor
    · intro heV
      have he_not_present : e ∉ present :=
        Finset.disjoint_left.mp hV_disj.symm heV
      have he_union : e ∈ present ∪ V' := by
        have : e ∈ present ∪ V := Finset.mem_union.mpr (Or.inr heV)
        simpa [hEq] using this
      rcases Finset.mem_union.mp he_union with he_present | heV'
      · exact False.elim (he_not_present he_present)
      · exact heV'
    · intro heV'
      have he_not_present : e ∉ present :=
        Finset.disjoint_left.mp hV'_disj.symm heV'
      have he_union : e ∈ present ∪ V := by
        have : e ∈ present ∪ V' := Finset.mem_union.mpr (Or.inr heV')
        simpa [hEq] using this
      rcases Finset.mem_union.mp he_union with he_present | heV
      · exact False.elim (he_not_present he_present)
      · exact heV
  have hterm_split :
      terminal.card = absent.card + upper.card := by
    have hsdiff := Finset.card_sdiff_of_subset habsent
    have hsdiff_upper : upper.card = terminal.card - absent.card := by
      simpa [upper] using hsdiff
    have hle := Finset.card_le_card habsent
    omega
  have hupper_split :
      upper.card = present.card + free.card := by
    have hsdiff := Finset.card_sdiff_of_subset hpresent_upper
    have hsdiff_free : free.card = upper.card - present.card := by
      simpa [free] using hsdiff
    have hle := Finset.card_le_card hpresent_upper
    omega
  have hterm_split_all :
      terminal.card = absent.card + present.card + free.card := by
    omega
  have hsum_eq :
      (terminal.powerset.filter W).sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card))
        =
        p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
    calc
      (terminal.powerset.filter W).sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card))
          =
        (Finset.Icc present upper).sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
          rw [hselected_eq]
      _ =
        ((upper \ present).powerset.image (fun V : Finset Coord => present ∪ V)).sum
          (fun A =>
            p ^ A.card *
              ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
          rw [Finset.Icc_eq_image_powerset hpresent_upper]
      _ =
        free.powerset.sum
          (fun V =>
            p ^ (present ∪ V).card *
              ((1 : ℝ) - p) ^ (terminal.card - (present ∪ V).card)) := by
          dsimp [free]
          rw [Finset.sum_image himage_inj]
      _ =
        free.powerset.sum
          (fun V =>
            (p ^ present.card * ((1 : ℝ) - p) ^ absent.card) *
              (p ^ V.card * ((1 : ℝ) - p) ^ (free.card - V.card))) := by
          refine Finset.sum_congr rfl ?_
          intro V hV
          have hV_subset : V ⊆ free := Finset.mem_powerset.mp hV
          have hV_disj : Disjoint present V :=
            disjoint_sdiff_self_right.mono_right hV_subset
          have hcard_union :
              (present ∪ V).card = present.card + V.card :=
            Finset.card_union_of_disjoint hV_disj
          have hV_card_le : V.card ≤ free.card :=
            Finset.card_le_card hV_subset
          have hterm_minus :
              terminal.card - (present ∪ V).card =
                absent.card + (free.card - V.card) := by
            omega
          rw [hterm_minus, hcard_union, pow_add, pow_add]
          ring
      _ =
        (p ^ present.card * ((1 : ℝ) - p) ^ absent.card) *
          free.powerset.sum
            (fun V =>
              p ^ V.card * ((1 : ℝ) - p) ^ (free.card - V.card)) := by
          rw [Finset.mul_sum]
      _ =
        (p ^ present.card * ((1 : ℝ) - p) ^ absent.card) *
          (p + ((1 : ℝ) - p)) ^ free.card := by
          rw [Finset.sum_pow_mul_eq_add_pow]
      _ =
        p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
          ring
  change TwoBiteConditionalProbability n m p cylinder hist ≤
    p ^ present.card * ((1 : ℝ) - p) ^ absent.card
  exact le_trans hpartition (le_of_eq hsum_eq)
