import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Ring
import Tablet.FinsetPowersetCylinderMass
import Tablet.Preamble

-- [TABLET NODE: FinsetBlueFiberRedSupportMass]

theorem FinsetBlueFiberRedSupportMass
    {α : Type} [DecidableEq α]
    (terminal blueTerminal R S : Finset α) (p : ℝ) (uR : ℕ)
    (hblueTerm : blueTerminal ⊆ terminal)
    (hSblue : S ⊆ blueTerminal)
    (hRterm : R ⊆ terminal)
    (hRcard : R.card = uR)
    (hRblue : Disjoint R blueTerminal) :
    (terminal.powerset.filter
        (fun A => A ∩ blueTerminal = S ∧ R ⊆ A)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
      =
      p ^ uR *
        (p ^ S.card * ((1 : ℝ) - p) ^ (blueTerminal.card - S.card)) := by
-- BODY
  classical
  let present : Finset α := R ∪ S
  let absent : Finset α := blueTerminal \ S
  have hpresent_term : present ⊆ terminal := by
    intro e he
    rcases Finset.mem_union.mp he with heR | heS
    · exact hRterm heR
    · exact hblueTerm (hSblue heS)
  have habsent_term : absent ⊆ terminal := by
    intro e he
    exact hblueTerm (Finset.mem_sdiff.mp he).1
  have hRSdisj : Disjoint R S :=
    hRblue.mono_right hSblue
  have hpresent_absent : Disjoint present absent := by
    change Disjoint (R ∪ S) (blueTerminal \ S)
    refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
    · exact hRblue.mono_right Finset.sdiff_subset
    · exact disjoint_sdiff_self_right
  have hfilter_eq :
      terminal.powerset.filter
          (fun A => A ∩ blueTerminal = S ∧ R ⊆ A)
        =
        terminal.powerset.filter
          (fun A => present ⊆ A ∧ Disjoint absent A) := by
    ext A
    constructor
    · intro hA
      rcases Finset.mem_filter.mp hA with ⟨hApow, hblue_eq, hRsub⟩
      refine Finset.mem_filter.mpr ⟨hApow, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_union.mp he with heR | heS
        · exact hRsub heR
        · have he_inter : e ∈ A ∩ blueTerminal := by
            simpa [hblue_eq] using heS
          exact (Finset.mem_inter.mp he_inter).1
      · rw [Finset.disjoint_left]
        intro e he_abs heA
        rcases Finset.mem_sdiff.mp he_abs with ⟨he_blue, he_not_S⟩
        have he_inter : e ∈ A ∩ blueTerminal :=
          Finset.mem_inter.mpr ⟨heA, he_blue⟩
        exact he_not_S (by simpa [hblue_eq] using he_inter)
    · intro hA
      rcases Finset.mem_filter.mp hA with ⟨hApow, hpresent_sub, habsent_disj⟩
      refine Finset.mem_filter.mpr ⟨hApow, ?_, ?_⟩
      · ext e
        constructor
        · intro he
          rcases Finset.mem_inter.mp he with ⟨heA, he_blue⟩
          by_contra he_not_S
          have he_abs : e ∈ absent :=
            Finset.mem_sdiff.mpr ⟨he_blue, he_not_S⟩
          exact (Finset.disjoint_left.mp habsent_disj he_abs) heA
        · intro heS
          have he_present : e ∈ present :=
            Finset.mem_union.mpr (Or.inr heS)
          exact Finset.mem_inter.mpr
            ⟨hpresent_sub he_present, hSblue heS⟩
      · intro e heR
        exact hpresent_sub (Finset.mem_union.mpr (Or.inl heR))
  have hpresent_card : present.card = uR + S.card := by
    have hcard : (R ∪ S).card = R.card + S.card :=
      Finset.card_union_of_disjoint hRSdisj
    simpa [present, hRcard] using hcard
  have habsent_card : absent.card = blueTerminal.card - S.card := by
    simpa [absent] using Finset.card_sdiff_of_subset hSblue
  calc
    (terminal.powerset.filter
        (fun A => A ∩ blueTerminal = S ∧ R ⊆ A)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card))
        =
      (terminal.powerset.filter
        (fun A => present ⊆ A ∧ Disjoint absent A)).sum
        (fun A => p ^ A.card * ((1 : ℝ) - p) ^ (terminal.card - A.card)) := by
        rw [hfilter_eq]
    _ =
      p ^ present.card * ((1 : ℝ) - p) ^ absent.card := by
        exact
          FinsetPowersetCylinderMass terminal present absent p
            hpresent_term habsent_term hpresent_absent
    _ =
      p ^ uR *
        (p ^ S.card * ((1 : ℝ) - p) ^ (blueTerminal.card - S.card)) := by
        rw [hpresent_card, habsent_card, pow_add]
        ring
