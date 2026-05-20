import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Tablet.TwoBiteEventProbabilityUnionBound
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: MediumClosedPairsFiniteCandidateUnionBound]

open scoped BigOperators

theorem MediumClosedPairsFiniteCandidateUnionBound {n m : ℕ} {p tail : ℝ}
    {ι : Type} [Fintype ι]
    (Bad : TwoBiteSample n m p → Prop)
    (Candidate : ι → TwoBiteSample n m p → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcover : ∀ ω : TwoBiteSample n m p, Bad ω → ∃ i : ι, Candidate i ω)
    (htail :
      ∀ i : ι, TwoBiteEventProbability n m p (Candidate i) ≤ tail) :
    TwoBiteEventProbability n m p Bad ≤
      (Fintype.card ι : ℝ) * tail := by
-- BODY
  classical
  have hmono :
      TwoBiteEventProbability n m p Bad ≤
        TwoBiteEventProbability n m p (fun ω => ∃ i : ι, Candidate i ω) := by
    unfold TwoBiteEventProbability
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hcover ω hω
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω hp0 hp1
  have hunion :
      TwoBiteEventProbability n m p (fun ω => ∃ i : ι, Candidate i ω) ≤
        ∑ i : ι, TwoBiteEventProbability n m p (Candidate i) :=
    TwoBiteEventProbabilityUnionBound hp0 hp1 Candidate
  have hsum_tail :
      (∑ i : ι, TwoBiteEventProbability n m p (Candidate i)) ≤
        ∑ _i : ι, tail := by
    exact Finset.sum_le_sum (fun i _hi => htail i)
  have htail_sum : (∑ _i : ι, tail) = (Fintype.card ι : ℝ) * tail := by
    simp [nsmul_eq_mul, mul_comm]
  calc
    TwoBiteEventProbability n m p Bad
        ≤ TwoBiteEventProbability n m p (fun ω => ∃ i : ι, Candidate i ω) := hmono
    _ ≤ ∑ i : ι, TwoBiteEventProbability n m p (Candidate i) := hunion
    _ ≤ ∑ _i : ι, tail := hsum_tail
    _ = (Fintype.card ι : ℝ) * tail := htail_sum
