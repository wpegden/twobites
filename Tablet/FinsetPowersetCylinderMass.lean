import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Ring
import Tablet.Preamble

-- [TABLET NODE: FinsetPowersetCylinderMass]

theorem FinsetPowersetCylinderMass
    {α : Type} [DecidableEq α]
    (terminal present absent : Finset α) (p : ℝ)
    (hpresent : present ⊆ terminal)
    (habsent : absent ⊆ terminal)
    (hdisj : Disjoint present absent) :
    (terminal.powerset.filter
        (fun A => present ⊆ A ∧ Disjoint absent A)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
      =
      p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
-- BODY
  classical
  let upper : Finset α := terminal \ absent
  let free : Finset α := upper \ present
  have hpresent_upper : present ⊆ upper := by
    exact (Finset.subset_sdiff).2 ⟨hpresent, hdisj⟩
  have hselected_eq :
      terminal.powerset.filter
        (fun A => present ⊆ A ∧ Disjoint absent A) = Finset.Icc present upper := by
    ext A
    simp [upper, Finset.Icc_eq_filter_powerset, Finset.subset_sdiff,
      and_assoc, and_left_comm, and_comm, disjoint_comm]
  have himage_inj :
      Set.InjOn (fun V : Finset α => present ∪ V) (free.powerset : Set (Finset α)) := by
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
  calc
    (terminal.powerset.filter
        (fun A => present ⊆ A ∧ Disjoint absent A)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
        =
      (Finset.Icc present upper).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
        rw [hselected_eq]
    _ =
      ((upper \ present).powerset.image (fun V : Finset α => present ∪ V)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
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
          (fun V => p ^ V.card * ((1 : ℝ) - p) ^ (free.card - V.card)) := by
        rw [Finset.mul_sum]
    _ =
      (p ^ present.card * ((1 : ℝ) - p) ^ absent.card) *
        (p + ((1 : ℝ) - p)) ^ free.card := by
        rw [Finset.sum_pow_mul_eq_add_pow]
    _ =
      p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
        ring
