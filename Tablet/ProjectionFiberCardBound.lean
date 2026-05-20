import Tablet.Preamble

-- [TABLET NODE: ProjectionFiberCardBound]

theorem ProjectionFiberCardBound :
    ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      (A : Finset α) (f : α → β) (F : ℝ),
      (∀ y, y ∈ A.image f →
        (((A.filter (fun x => f x = y)).card : ℝ) ≤ F)) →
      (A.card : ℝ) ≤ F * ((A.image f).card : ℝ) := by
-- BODY
  classical
  intro α β _ _ A f F hfiber
  let fiber : β → Finset α := fun y => A.filter (fun x => f x = y)
  have hA_to_sigma :
      A.card ≤ ((A.image f).sigma fiber).card := by
    refine Finset.card_le_card_of_injOn
      (fun x : α => (⟨f x, x⟩ : Sigma fun _ : β => α)) ?_ ?_
    · intro x hx
      have hxA : x ∈ A := by simpa using hx
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_image.mpr ⟨x, hxA, rfl⟩, by
          simp [fiber, hxA]⟩
    · intro x _hx y _hy hEq
      exact congrArg Sigma.snd hEq
  have hA_le_sum_nat :
      A.card ≤ (A.image f).sum (fun y => (fiber y).card) := by
    simpa [Finset.card_sigma] using hA_to_sigma
  have hA_le_sum :
      (A.card : ℝ) ≤
        (A.image f).sum (fun y => ((fiber y).card : ℝ)) := by
    exact_mod_cast hA_le_sum_nat
  have hsum_le :
      (A.image f).sum (fun y => ((fiber y).card : ℝ)) ≤
        (A.image f).sum (fun _y => F) := by
    exact Finset.sum_le_sum (fun y hy => by simpa [fiber] using hfiber y hy)
  calc
    (A.card : ℝ) ≤ (A.image f).sum (fun y => ((fiber y).card : ℝ)) := hA_le_sum
    _ ≤ (A.image f).sum (fun _y => F) := hsum_le
    _ = F * ((A.image f).card : ℝ) := by
      simp [nsmul_eq_mul, mul_comm]
