import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteBlueGraph
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne

open Classical

-- [TABLET NODE: TwoBiteBlueMarginal]

theorem TwoBiteBlueMarginal (n m : ℕ) (p : ℝ) (hn : n ≤ m * m)
    (E : SimpleGraph (Fin m) → Prop) [DecidablePred E] :
    TwoBiteEventProbability n m p (fun ω => E (TwoBiteBlueGraph ω)) =
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
  simp only [TwoBiteBlueGraph, TwoBiteSampleWeight, TwoBiteSample]
  change
    (∑ x : A × A × C,
        if E x.2.1 then
          GnpGraphWeight p x.1 * GnpGraphWeight p x.2.1 * UniformInjectionWeight n m
        else 0) =
      ∑ G : A, if E G then GnpGraphWeight p G else 0
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hInner :
      ∀ x_B : A,
        (∑ x_R : A, ∑ π : C,
            (GnpGraphWeight p x_R * GnpGraphWeight p x_B * UniformInjectionWeight n m)) =
          GnpGraphWeight p x_B := by
    intro x_B
    calc
      (∑ x_R : A, ∑ π : C,
          (GnpGraphWeight p x_R * GnpGraphWeight p x_B * UniformInjectionWeight n m))
          = ∑ x_R : A,
              GnpGraphWeight p x_R * GnpGraphWeight p x_B *
                (∑ π : C, UniformInjectionWeight n m) := by
            simp_rw [← Finset.mul_sum]
      _ = ∑ x_R : A, GnpGraphWeight p x_R * GnpGraphWeight p x_B := by
            simp [hUniform]
      _ = (∑ x_R : A, GnpGraphWeight p x_R) * GnpGraphWeight p x_B := by
            rw [Finset.sum_mul]
      _ = GnpGraphWeight p x_B := by
            rw [GnpGraphWeightSumOne m p, one_mul]
  apply Finset.sum_congr rfl
  intro x_B hxB
  split_ifs with hE
  · exact hInner x_B
  · simp
