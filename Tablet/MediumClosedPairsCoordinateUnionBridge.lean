import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteEventProbabilityUnionBound

-- [TABLET NODE: MediumClosedPairsCoordinateUnionBridge]

open scoped BigOperators

theorem MediumClosedPairsCoordinateUnionBridge
    {n m t N : ℕ} {p : ℝ}
    (C : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hCcard : C.card ≤ N)
    (hfixed :
      ∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ∈ C.powersetCard t →
          TwoBiteEventProbability n m p
            (fun ω => ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e) ≤
              p ^ t) :
    TwoBiteEventProbability n m p
      (fun ω =>
        t ≤
          (@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
            (fun e => TwoBiteEdgeCoordinateValue ω e)
            (Classical.decPred _) C).card)
      ≤ (Nat.choose N t : ℝ) * p ^ t := by
-- BODY
  classical
  let Coord := Sum (Fin m × Fin m) (Fin m × Fin m)
  let ι := {A : Finset Coord // A ∈ C.powersetCard t}
  let Candidate : ι → TwoBiteSample n m p → Prop :=
    fun A ω => ∀ e, e ∈ (A : Finset Coord) → TwoBiteEdgeCoordinateValue ω e
  have hcover :
      ∀ ω : TwoBiteSample n m p,
        t ≤
          (@Finset.filter Coord
            (fun e => TwoBiteEdgeCoordinateValue ω e)
            (Classical.decPred _) C).card →
          ∃ A : ι, Candidate A ω := by
    intro ω hω
    let present : Finset Coord :=
      @Finset.filter Coord
        (fun e => TwoBiteEdgeCoordinateValue ω e)
        (Classical.decPred _) C
    obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq (s := present) hω
    have hA_mem : A ∈ C.powersetCard t := by
      rw [Finset.mem_powersetCard]
      constructor
      · intro e heA
        exact (Finset.mem_filter.mp (hA_sub heA)).1
      · exact hA_card
    refine ⟨⟨A, hA_mem⟩, ?_⟩
    intro e heA
    exact (Finset.mem_filter.mp (hA_sub heA)).2
  have hmono :
      TwoBiteEventProbability n m p
          (fun ω =>
            t ≤
              (@Finset.filter Coord
                (fun e => TwoBiteEdgeCoordinateValue ω e)
                (Classical.decPred _) C).card)
        ≤ TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω) := by
    unfold TwoBiteEventProbability
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hcover ω hω
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hunion :
      TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω)
        ≤ ∑ A : ι, TwoBiteEventProbability n m p (Candidate A) :=
    TwoBiteEventProbabilityUnionBound hp0 hp1 Candidate
  have hsum_tail :
      (∑ A : ι, TwoBiteEventProbability n m p (Candidate A)) ≤
        ∑ _A : ι, p ^ t := by
    refine Finset.sum_le_sum ?_
    intro A _hA
    exact hfixed (A : Finset Coord) A.property
  have htail_sum : (∑ _A : ι, p ^ t) = ((C.powersetCard t).card : ℝ) * p ^ t := by
    simp [ι, nsmul_eq_mul]
  have hcard_choose : ((C.powersetCard t).card : ℝ) = (Nat.choose C.card t : ℝ) := by
    rw [Finset.card_powersetCard]
  have hchoose_le : (Nat.choose C.card t : ℝ) ≤ (Nat.choose N t : ℝ) := by
    exact_mod_cast Nat.choose_le_choose t hCcard
  have hpow_nonneg : 0 ≤ p ^ t := pow_nonneg hp0 t
  calc
    TwoBiteEventProbability n m p
        (fun ω =>
          t ≤
            (@Finset.filter Coord
              (fun e => TwoBiteEdgeCoordinateValue ω e)
              (Classical.decPred _) C).card)
        ≤ TwoBiteEventProbability n m p (fun ω => ∃ A : ι, Candidate A ω) := hmono
    _ ≤ ∑ A : ι, TwoBiteEventProbability n m p (Candidate A) := hunion
    _ ≤ ∑ _A : ι, p ^ t := hsum_tail
    _ = ((C.powersetCard t).card : ℝ) * p ^ t := htail_sum
    _ = (Nat.choose C.card t : ℝ) * p ^ t := by rw [hcard_choose]
    _ ≤ (Nat.choose N t : ℝ) * p ^ t := by
      exact mul_le_mul_of_nonneg_right hchoose_le hpow_nonneg
