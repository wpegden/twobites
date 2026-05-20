import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteRedGraph
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne

open Classical

-- [TABLET NODE: TwoBiteRedMarginal]

theorem TwoBiteRedMarginal (n m : ℕ) (p : ℝ) (hn : n ≤ m * m)
    (E : SimpleGraph (Fin m) → Prop) [DecidablePred E] :
    TwoBiteEventProbability n m p (fun ω => E (TwoBiteRedGraph ω)) =
      ∑ G : SimpleGraph (Fin m), if E G then GnpGraphWeight p G else 0 := by
-- BODY
  classical
  let A := SimpleGraph (Fin m)
  let C := Fin n ↪ (Fin m × Fin m)
  have hCnonempty : Nonempty C := by
    let e : Fin m × Fin m ≃ Fin (m * m) := finProdFinEquiv
    exact ⟨(Fin.castLEEmb hn).trans e.symm.toEmbedding⟩
  have hCcard_ne : Fintype.card C ≠ 0 := by
    classical
    exact Fintype.card_ne_zero
  have hCcard_real_ne : (Fintype.card C : ℝ) ≠ 0 := by
    exact_mod_cast hCcard_ne
  have hUniform :
      (∑ π : C, UniformInjectionWeight n m) = 1 := by
    rw [show (∑ π : C, UniformInjectionWeight n m) =
        (Fintype.card C : ℝ) * UniformInjectionWeight n m by simp]
    unfold UniformInjectionWeight
    rw [if_neg hCcard_ne]
    exact mul_inv_cancel₀ hCcard_real_ne
  unfold TwoBiteEventProbability
  rw [Finset.sum_filter]
  simp only [TwoBiteRedGraph, TwoBiteSampleWeight, TwoBiteSample]
  change
    (∑ x : A × A × C,
        if E x.1 then
          GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m
        else 0) =
      ∑ G : A, if E G then GnpGraphWeight p G else 0
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hCard_uniform :
      (Fintype.card C : ℝ) * UniformInjectionWeight n m = 1 := by
    simpa using hUniform
  have hInner :
      ∀ x : A,
        (∑ x_1 : A,
            (Fintype.card C : ℝ) *
              (GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m)) =
          GnpGraphWeight p x := by
    intro x
    calc
      (∑ x_1 : A,
          (Fintype.card C : ℝ) *
            (GnpGraphWeight p x * GnpGraphWeight p x_1 * UniformInjectionWeight n m))
          = ∑ x_1 : A,
              GnpGraphWeight p x * GnpGraphWeight p x_1 *
                ((Fintype.card C : ℝ) * UniformInjectionWeight n m) := by
            apply Finset.sum_congr rfl
            intro x_1 hx_1
            ring
      _ = ∑ x_1 : A, GnpGraphWeight p x * GnpGraphWeight p x_1 := by
            simp [hCard_uniform]
      _ = GnpGraphWeight p x := by
            rw [← Finset.mul_sum]
            rw [GnpGraphWeightSumOne m p, mul_one]
  simp [hInner]
