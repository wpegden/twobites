import Tablet.Preamble
import Mathlib.Data.Fintype.Perm
import Tablet.MajorizationTwoCoordinateAbsRearrangement

open Finset Equiv Equiv.Perm

-- [TABLET NODE: MajorizationAdjacentSwapDistance]

theorem MajorizationAdjacentSwapDistance (N : ℕ) (b u : Fin N → ℝ)
    (hb : ∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i)
    (r : Fin N) (hr : r.val + 1 < N)
    (hu : u r < u ⟨r.val + 1, hr⟩) :
    ∑ i, |(u ∘ ⇑(swap r ⟨r.val + 1, hr⟩)) i - b i| ≤ ∑ i, |u i - b i| := by
-- BODY
  let r_next : Fin N := ⟨r.val + 1, hr⟩
  have hr_neq : r ≠ r_next := by
    intro h_eq
    have : r.val = r_next.val := Fin.ext_iff.mp h_eq
    dsimp [r_next] at this
    linarith
  have sum_insert_two : ∀ (f : Fin N → ℝ), ∑ i, f i = f r + f r_next + ∑ i ∈ univ \ {r, r_next}, f i := by
    intro f
    have eq_univ : (univ : Finset (Fin N)) = insert r (insert r_next (univ \ {r, r_next})) := by
      ext x
      simp
      tauto
    nth_rw 1 [eq_univ]
    have h1 : r ∉ insert r_next (univ \ {r, r_next}) := by simp [hr_neq]
    rw [sum_insert h1]
    have h2 : r_next ∉ univ \ {r, r_next} := by simp
    rw [sum_insert h2]
    rw [add_assoc]
  have eq1 := sum_insert_two (fun i => |u i - b i|)
  have eq2 := sum_insert_two (fun i => |(u ∘ ⇑(swap r r_next)) i - b i|)
  have eq2_simp : ∑ i, |(u ∘ ⇑(swap r r_next)) i - b i| = |u r_next - b r| + |u r - b r_next| + ∑ i ∈ univ \ {r, r_next}, |u i - b i| := by
    rw [eq2]
    have h_r : |(u ∘ ⇑(swap r r_next)) r - b r| = |u r_next - b r| := by dsimp; rw [swap_apply_left]
    have h_next : |(u ∘ ⇑(swap r r_next)) r_next - b r_next| = |u r - b r_next| := by dsimp; rw [swap_apply_right]
    rw [h_r, h_next]
    have h_rest : ∑ i ∈ univ \ {r, r_next}, |(u ∘ ⇑(swap r r_next)) i - b i| = ∑ i ∈ univ \ {r, r_next}, |u i - b i| := by
      apply sum_congr rfl
      intro x hx
      simp at hx
      dsimp
      rw [swap_apply_of_ne_of_ne hx.1 hx.2]
    rw [h_rest]
  rw [eq1, eq2_simp]
  have H := MajorizationTwoCoordinateAbsRearrangement (le_of_lt hu) (hb r r_next (by simp [r_next]))
  linarith
