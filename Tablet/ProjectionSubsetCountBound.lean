import Tablet.Preamble
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

open Finset
open BigOperators

-- [TABLET NODE: ProjectionSubsetCountBound]

theorem ProjectionSubsetCountBound {m k ℓR ℓB : ℕ} :
    (Finset.univ.filter (fun S : Finset (Fin m × Fin m) =>
      S.card = k ∧
      (S.image Prod.fst).card = ℓR ∧
      (S.image Prod.snd).card = ℓB)).card
    ≤ Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k := by
-- BODY
  let X := (univ : Finset (Finset (Fin m × Fin m))).filter (fun S =>
      S.card = k ∧ (S.image Prod.fst).card = ℓR ∧ (S.image Prod.snd).card = ℓB)
  let Rs := powersetCard ℓR (univ : Finset (Fin m))
  let Bs := powersetCard ℓB (univ : Finset (Fin m))
  let Y := Rs.biUnion (fun R => Bs.biUnion (fun B => powersetCard k (R ×ˢ B)))

  have hX : X ⊆ Y := by
    intro S hS
    unfold X at hS
    simp only [mem_filter, mem_univ, true_and] at hS
    rcases hS with ⟨hk, hRcard, hBcard⟩
    unfold Y
    simp only [mem_biUnion, mem_powersetCard]
    use S.image Prod.fst
    constructor
    · apply mem_powersetCard.mpr
      exact ⟨subset_univ _, hRcard⟩
    use S.image Prod.snd
    constructor
    · apply mem_powersetCard.mpr
      exact ⟨subset_univ _, hBcard⟩
    constructor
    · intro x hx
      simp only [mem_product]
      exact ⟨mem_image_of_mem _ hx, mem_image_of_mem _ hx⟩
    · exact hk

  calc X.card ≤ Y.card := card_le_card hX
    _ ≤ Rs.sum (fun R => (Bs.biUnion (fun B => powersetCard k (R ×ˢ B))).card) := card_biUnion_le
    _ ≤ Rs.sum (fun R => Bs.sum (fun B => (powersetCard k (R ×ˢ B)).card)) := by
      apply sum_le_sum
      intro R _
      apply card_biUnion_le
    _ = Rs.sum (fun R => Bs.sum (fun B => Nat.choose (R.card * B.card) k)) := by
      simp only [card_powersetCard, card_product]
    _ = Rs.sum (fun R => Bs.sum (fun B => Nat.choose (ℓR * ℓB) k)) := by
      apply sum_congr rfl
      intro R hR
      apply sum_congr rfl
      intro B hB
      rw [(mem_powersetCard.1 hR).2, (mem_powersetCard.1 hB).2]
    _ = Rs.card * Bs.card * Nat.choose (ℓR * ℓB) k := by
      simp only [sum_const, nsmul_eq_mul]
      change Rs.card * (Bs.card * Nat.choose (ℓR * ℓB) k) = Rs.card * Bs.card * Nat.choose (ℓR * ℓB) k
      rw [Nat.mul_assoc]
    _ = Nat.choose m ℓR * Nat.choose m ℓB * Nat.choose (ℓR * ℓB) k := by
      unfold Rs Bs
      simp only [card_powersetCard, card_univ, Fintype.card_fin]
