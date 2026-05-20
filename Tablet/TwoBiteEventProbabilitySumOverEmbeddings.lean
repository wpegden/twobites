import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.TwoBiteEmbedding
import Tablet.TwoBiteEventProbabilityTotalMassBound

-- [TABLET NODE: TwoBiteEventProbabilitySumOverEmbeddings]

theorem TwoBiteEventProbabilitySumOverEmbeddings
    {n m : ℕ} {p : ℝ} (event : TwoBiteSample n m p → Prop)
    (P_bound : ℝ)
    (h_le : ∀ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π ∧ event ω)
      ≤ P_bound * TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π))
    (h_P_bound_nonneg : 0 ≤ P_bound) :
    TwoBiteEventProbability n m p event ≤ P_bound := by
-- BODY
  classical
  have part_lemma : ∀ (event' : TwoBiteSample n m p → Prop),
    TwoBiteEventProbability n m p event' =
      ∑ a : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = a ∧ event' ω) := by
    intro event'
    unfold TwoBiteEventProbability
    have h_cov' : ∀ i ∈ Finset.univ.filter event', TwoBiteEmbedding i ∈ (@Finset.univ (Fin n ↪ (Fin m × Fin m)) _) := fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to h_cov']
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr
    · ext x
      simp [and_comm]
    · intro _ _
      rfl
  have h_part_event : TwoBiteEventProbability n m p event =
      ∑ j : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = j ∧ event ω) := part_lemma event
  rw [h_part_event]
  have h1 : ∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π ∧ event ω)
      ≤ ∑ π : Fin n ↪ (Fin m × Fin m), P_bound * TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π) := by
    apply Finset.sum_le_sum
    intro π _
    exact h_le π
  have h2 : ∑ π : Fin n ↪ (Fin m × Fin m), P_bound * TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π)
      = P_bound * ∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π) := by
    rw [Finset.mul_sum]
  rw [h2] at h1
  have h_part_true : TwoBiteEventProbability n m p (fun ω : TwoBiteSample n m p => True) =
      ∑ j : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = j ∧ True) := part_lemma (fun _ => True)
  have h_true_le_1 := TwoBiteEventProbabilityTotalMassBound n m p
  have h_sum_le_1 : (∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π)) ≤ 1 := by
    have eq_part : (∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π)) = ∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π ∧ True) := by
      apply Finset.sum_congr rfl
      intro π _
      congr
      ext ω
      simp
    rw [eq_part]
    rw [← h_part_true]
    exact h_true_le_1
  have h3 : P_bound * ∑ π : Fin n ↪ (Fin m × Fin m), TwoBiteEventProbability n m p (fun ω => TwoBiteEmbedding ω = π) ≤ P_bound * 1 := by
    apply mul_le_mul_of_nonneg_left h_sum_le_1 h_P_bound_nonneg
  rw [mul_one] at h3
  exact le_trans h1 h3
