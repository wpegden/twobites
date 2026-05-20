import Tablet.FixedSetProductModelMass
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod

open scoped Classical
open scoped BigOperators

-- [TABLET NODE: FixedSetProductModelWeightSum]

theorem FixedSetProductModelWeightSum {m_sub : ℕ} (p_sub : ℝ) (P_R P_B : Finset (Fin m_sub))
    (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1) :
    let q := FixedSetProductModelMassFn p_sub P_R P_B
    let r_prod := 2 * m_sub
    Finset.univ.sum (fun v : Fin r_prod → Finset (Fin m_sub) × Finset (Fin m_sub) =>
      Finset.univ.prod (fun i => q (v i))) = 1 := by
-- BODY
  dsimp only
  let q := FixedSetProductModelMassFn p_sub P_R P_B
  let α := Finset (Fin m_sub) × Finset (Fin m_sub)
  have h_sum : ∑ a : α, q a = 1 := (FixedSetProductModelMass p_sub hp0 hp1 P_R P_B).2
  -- Use sum_pow' which relates (∑ f)^n to ∑ ∏ f
  -- We need to show that Finset.univ is Fintype.piFinset (fun _ => univ)
  let s := (Finset.univ : Finset α)
  have h_univ : (Finset.univ : Finset (Fin (2 * m_sub) → α)) = Fintype.piFinset (fun _ : Fin (2 * m_sub) => s) := by
    apply Finset.eq_univ_of_forall
    intro x
    simp
  rw [h_univ]
  rw [← Finset.sum_pow']
  rw [h_sum]
  simp
