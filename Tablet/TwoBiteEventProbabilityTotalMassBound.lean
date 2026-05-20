import Tablet.TwoBiteEventProbability
import Tablet.GnpGraphWeightSumOne

-- [TABLET NODE: TwoBiteEventProbabilityTotalMassBound]

theorem TwoBiteEventProbabilityTotalMassBound :
    ∀ (n m : ℕ) (p : ℝ),
      TwoBiteEventProbability n m p (fun _ => True) ≤ 1 := by
-- BODY
  intro n m p
  classical
  let A := SimpleGraph (Fin m)
  let C := Fin n ↪ (Fin m × Fin m)
  let W : A → ℝ := fun G => GnpGraphWeight p G
  let U : C → ℝ := fun _ => UniformInjectionWeight n m
  have hU : Finset.univ.sum U ≤ 1 := by
    unfold U UniformInjectionWeight
    split_ifs with hzero
    · simp
    · rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_ne : (Fintype.card C : ℝ) ≠ 0 := by
        exact_mod_cast hzero
      field_simp [hcard_ne]
      simp [C]
  have hfactor :
      (Finset.univ.sum
        (fun x : A × (A × C) => W x.1 * W x.2.1 * U x.2.2)) =
        (Finset.univ.sum W) * (Finset.univ.sum W) * (Finset.univ.sum U) := by
    calc
      Finset.univ.sum
          (fun x : A × (A × C) => W x.1 * W x.2.1 * U x.2.2)
          = ∑ a : A, ∑ y : A × C, W a * W y.1 * U y.2 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = ∑ a : A, W a * (∑ y : A × C, W y.1 * U y.2) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro y hy
            ring
      _ = (∑ a : A, W a) * (∑ y : A × C, W y.1 * U y.2) := by
            rw [Finset.sum_mul]
      _ = (∑ a : A, W a) *
            (∑ b : A, ∑ c : C, W b * U c) := by
            congr 1
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = (∑ a : A, W a) *
            (∑ b : A, W b * (∑ c : C, U c)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [Finset.mul_sum]
      _ = (∑ a : A, W a) *
            ((∑ b : A, W b) * (∑ c : C, U c)) := by
            congr 1
            rw [Finset.sum_mul]
      _ = (Finset.univ.sum W) * (Finset.univ.sum W) * (Finset.univ.sum U) := by
            ring
  unfold TwoBiteEventProbability TwoBiteSampleWeight
  simp only [Finset.filter_true]
  change (Finset.univ.sum
        (fun x : A × (A × C) => W x.1 * W x.2.1 * U x.2.2)) ≤ 1
  rw [hfactor]
  have hW : Finset.univ.sum W = 1 := by
    simpa [W, A] using GnpGraphWeightSumOne m p
  rw [hW]
  simpa using hU
