import Tablet.TwoBiteEventProbability
import Tablet.GnpGraphWeightSumOne
import Tablet.UniformInjectionWeight

-- [TABLET NODE: TwoBiteEventProbabilityInjectionOnly]

open Classical

lemma TwoBiteEventProbabilityInjectionOnly {n m : ℕ} {p : ℝ}
    (event : (Fin n ↪ Fin m × Fin m) → Prop) :
    TwoBiteEventProbability n m p (fun ω => event ω.2.2) =
    (Finset.univ.filter event).card * UniformInjectionWeight n m := by
-- BODY
  let A := SimpleGraph (Fin m)
  let C := Fin n ↪ (Fin m × Fin m)
  let W : A → ℝ := fun G => GnpGraphWeight p G
  let U : C → ℝ := fun _ => UniformInjectionWeight n m
  have hW : Finset.univ.sum W = 1 := by
    simpa [W, A] using GnpGraphWeightSumOne m p
  unfold TwoBiteEventProbability TwoBiteSampleWeight
  have hfactor :
      (Finset.univ.filter (fun x : A × (A × C) => event x.2.2)).sum
        (fun x => W x.1 * W x.2.1 * U x.2.2) =
        (Finset.univ.filter event).sum U := by
    calc
      _ = ∑ x : A × (A × C), if event x.2.2 then W x.1 * W x.2.1 * U x.2.2 else 0 := by
        rw [Finset.sum_filter]
      _ = ∑ a : A, ∑ y : A × C, if event y.2 then W a * W y.1 * U y.2 else 0 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ a : A, W a * (∑ y : A × C, if event y.2 then W y.1 * U y.2 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro y hy
        split_ifs
        · ring
        · simp
      _ = (∑ a : A, W a) * (∑ y : A × C, if event y.2 then W y.1 * U y.2 else 0) := by
        rw [Finset.sum_mul]
      _ = 1 * (∑ b : A, ∑ c : C, if event c then W b * U c else 0) := by
        rw [hW, ← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ b : A, W b * (∑ c : C, if event c then U c else 0) := by
        simp only [one_mul]
        refine Finset.sum_congr rfl ?_
        intro b hb
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro c hc
        split_ifs
        · ring
        · simp
      _ = (∑ b : A, W b) * (∑ c : C, if event c then U c else 0) := by
        rw [Finset.sum_mul]
      _ = ∑ c : C, if event c then U c else 0 := by
        rw [hW, one_mul]
      _ = (Finset.univ.filter event).sum U := by
        rw [Finset.sum_filter]
  rw [hfactor]
  unfold U
  rw [Finset.sum_const, nsmul_eq_mul]
