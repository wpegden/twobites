import Tablet.FiberAndDegreeFiberSizeInjectionMarginal
import Tablet.FiberAndDegreeFiberSizeImageHypergeometricLowerTail
import Tablet.FiberAndDegreeFiberSizeImageHypergeometricUpperTailChernoff
import Tablet.UniformInjectionWeight

open Finset Classical

-- [TABLET NODE: FiberAndDegreeFixedFiberTailProbability]

theorem FiberAndDegreeFixedFiberTailProbability {n m : ℕ} {p : ℝ}
    (redSide : Bool) (x : Fin m)
    (δ : ℝ) (h_support : n ≤ m * m) (hm_pos : 0 < m)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ (1 / 2 : ℝ)) :
    let μ : ℝ := (n : ℝ) / (m : ℝ)
    TwoBiteEventProbability n m p
      (fun ω => (1 + δ) * μ <
        (((if redSide then RedFiber ω x else BlueFiber ω x).card : ℕ) : ℝ))
      ≤ Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) ∧
    TwoBiteEventProbability n m p
      (fun ω =>
        ((((if redSide then RedFiber ω x else BlueFiber ω x).card : ℕ) : ℝ) <
          (1 - δ) * μ))
      ≤ Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
-- BODY
  classical
  intro μ
  let K : Finset (Fin m × Fin m) :=
    Finset.univ.filter (fun y => if redSide then y.1 = x else y.2 = x)
  have hK : K.card = m := by
    cases redSide
    · have hK_eq : K = (Finset.univ.image (fun r : Fin m => (r, x))) := by
        ext y
        constructor
        · intro hy
          have hy2 : y.2 = x := by
            simpa [K] using (Finset.mem_filter.mp hy).2
          exact Finset.mem_image.mpr ⟨y.1, Finset.mem_univ _, by ext <;> simp [hy2]⟩
        · intro hy
          rcases Finset.mem_image.mp hy with ⟨r, -, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
      rw [hK_eq]
      have hinj : Function.Injective (fun r : Fin m => (r, x)) := by
        intro a b h
        exact congrArg Prod.fst h
      rw [Finset.card_image_of_injective _ hinj]
      simp
    · have hK_eq : K = (Finset.univ.image (fun b : Fin m => (x, b))) := by
        ext y
        constructor
        · intro hy
          have hy1 : y.1 = x := by
            simpa [K] using (Finset.mem_filter.mp hy).2
          exact Finset.mem_image.mpr ⟨y.2, Finset.mem_univ _, by ext <;> simp [hy1]⟩
        · intro hy
          rcases Finset.mem_image.mp hy with ⟨b, -, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩
      rw [hK_eq]
      have hinj : Function.Injective (fun b : Fin m => (x, b)) := by
        intro a b h
        exact congrArg Prod.snd h
      rw [Finset.card_image_of_injective _ hinj]
      simp
  have h_nonempty : Nonempty (Fin n ↪ (Fin m × Fin m)) := by
    have hle_card :
        Fintype.card (Fin n) ≤ Fintype.card (Fin m × Fin m) := by
      simpa [Fintype.card_fin, Fintype.card_prod] using h_support
    exact Function.Embedding.nonempty_of_card_le hle_card
  have htotal_pos : 0 < (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr h_nonempty
  have htotal_ne_nat : Fintype.card (Fin n ↪ (Fin m × Fin m)) ≠ 0 :=
    Nat.ne_of_gt (Fintype.card_pos_iff.mpr h_nonempty)
  have hU :
      UniformInjectionWeight n m =
        (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
    unfold UniformInjectionWeight
    rw [if_neg htotal_ne_nat]
  have h_count :
      ∀ π : Fin n ↪ (Fin m × Fin m),
        ((Finset.univ.filter
          (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card : ℝ)
        =
        ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card : ℝ) := by
    intro π
    have himage :
        ((Finset.univ.filter
          (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).image π)
          =
        (((Finset.univ : Finset (Fin n)).image π) ∩ K) := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨a, ha, hπ⟩
        have hpred :
            if redSide then (π a).1 = x else (π a).2 = x := by
          simpa using (Finset.mem_filter.mp ha).2
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨a, Finset.mem_univ _, hπ⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [K, ← hπ] using hpred⟩⟩
      · intro hy
        rcases Finset.mem_inter.mp hy with ⟨hyimg, hyK⟩
        rcases Finset.mem_image.mp hyimg with ⟨a, -, hπ⟩
        have hpred_y :
            if redSide then y.1 = x else y.2 = x := by
          simpa [K] using (Finset.mem_filter.mp hyK).2
        exact Finset.mem_image.mpr
          ⟨a,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, by simpa [hπ] using hpred_y⟩,
            hπ⟩
    have hnat :
        (Finset.univ.filter
          (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card
        =
        ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card) := by
      rw [← himage]
      exact (Finset.card_image_of_injective _ π.injective).symm
    exact_mod_cast hnat
  constructor
  · have hmarg := FiberAndDegreeFiberSizeInjectionMarginal
      (n := n) (m := m) (p := p) redSide x
      (fun k : ℕ => (1 + δ) * μ < (k : ℝ))
    have hfilter :
        ((Finset.univ.filter
          (fun π : Fin n ↪ (Fin m × Fin m) =>
            (1 + δ) * μ <
              ((Finset.univ.filter
                (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card : ℝ))).card : ℝ)
        =
        ((Finset.univ.filter
          (fun π : Fin n ↪ (Fin m × Fin m) =>
            (1 + δ) * μ <
              ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card : ℝ))).card : ℝ) := by
      apply congrArg (fun S : Finset (Fin n ↪ (Fin m × Fin m)) => (S.card : ℝ))
      ext π
      simp [h_count π]
    have htail :=
      FiberAndDegreeFiberSizeImageHypergeometricUpperTailChernoff
        n m K hK δ h_support hm_pos hδ_pos
    calc
      TwoBiteEventProbability n m p
        (fun ω => (1 + δ) * μ <
          (((if redSide then RedFiber ω x else BlueFiber ω x).card : ℕ) : ℝ))
          =
          ((Finset.univ.filter
            (fun π : Fin n ↪ (Fin m × Fin m) =>
              (1 + δ) * μ <
                ((Finset.univ.filter
                  (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card : ℝ))).card : ℝ)
            * UniformInjectionWeight n m := by
            simpa [μ] using hmarg
      _ =
          ((Finset.univ.filter
            (fun π : Fin n ↪ (Fin m × Fin m) =>
              (1 + δ) * μ <
                ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card : ℝ))).card : ℝ)
            * (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
            rw [hfilter, hU]
      _ ≤ (Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) *
            (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)) *
            (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right (by simpa [μ] using htail) (inv_nonneg.mpr htotal_pos.le)
      _ = Real.exp (-(((1 + δ) * Real.log (1 + δ) - δ) * μ)) := by
            field_simp [htotal_pos.ne']
  · have hmarg := FiberAndDegreeFiberSizeInjectionMarginal
      (n := n) (m := m) (p := p) redSide x
      (fun k : ℕ => (k : ℝ) < (1 - δ) * μ)
    have hfilter :
        ((Finset.univ.filter
          (fun π : Fin n ↪ (Fin m × Fin m) =>
            ((Finset.univ.filter
              (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card : ℝ) <
                (1 - δ) * μ)).card : ℝ)
        =
        ((Finset.univ.filter
          (fun π : Fin n ↪ (Fin m × Fin m) =>
            ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card : ℝ) <
                (1 - δ) * μ)).card : ℝ) := by
      apply congrArg (fun S : Finset (Fin n ↪ (Fin m × Fin m)) => (S.card : ℝ))
      ext π
      simp [h_count π]
    have htail :=
      FiberAndDegreeFiberSizeImageHypergeometricLowerTail
        n m K hK δ h_support hm_pos hδ_pos hδ_le
    calc
      TwoBiteEventProbability n m p
        (fun ω =>
          ((((if redSide then RedFiber ω x else BlueFiber ω x).card : ℕ) : ℝ) <
            (1 - δ) * μ))
          =
          ((Finset.univ.filter
            (fun π : Fin n ↪ (Fin m × Fin m) =>
              ((Finset.univ.filter
                (fun v : Fin n => if redSide then (π v).1 = x else (π v).2 = x)).card : ℝ) <
                  (1 - δ) * μ)).card : ℝ)
            * UniformInjectionWeight n m := by
            simpa [μ] using hmarg
      _ =
          ((Finset.univ.filter
            (fun π : Fin n ↪ (Fin m × Fin m) =>
              ((((Finset.univ : Finset (Fin n)).image π) ∩ K).card : ℝ) <
                  (1 - δ) * μ)).card : ℝ)
            * (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
            rw [hfilter, hU]
      _ ≤ (Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) *
            (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)) *
            (Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right (by simpa [μ] using htail) (inv_nonneg.mpr htotal_pos.le)
      _ = Real.exp (-(δ + (1 - δ) * Real.log (1 - δ)) * μ) := by
            field_simp [htotal_pos.ne']
