import Tablet.Preamble
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- [TABLET NODE: CommonUnionCardDifferenceBound]

open scoped Classical

lemma CommonUnionCardDifferenceBound {α : Type} [DecidableEq α] (U A B : Finset α) :
    |(((U ∪ A).card : ℝ) - ((U ∪ B).card : ℝ))| ≤
      max ((A.card : ℝ)) ((B.card : ℝ)) := by
-- BODY
  classical
  have hUA :
      (U ∪ A).card = U.card + (A \ U).card := by
    have h_eq : U ∪ A = U ∪ (A \ U) := by
      ext x
      simp
    rw [h_eq]
    rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  have hUB :
      (U ∪ B).card = U.card + (B \ U).card := by
    have h_eq : U ∪ B = U ∪ (B \ U) := by
      ext x
      simp
    rw [h_eq]
    rw [Finset.card_union_of_disjoint Finset.disjoint_sdiff]
  have hsdA : (A \ U).card ≤ A.card := Finset.card_le_card Finset.sdiff_subset
  have hsdB : (B \ U).card ≤ B.card := Finset.card_le_card Finset.sdiff_subset
  rw [hUA, hUB]
  push_cast
  have h_abs :
      |(((A \ U).card : ℝ) - ((B \ U).card : ℝ))| ≤
        max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) := by
    have h1 :
        ((A \ U).card : ℝ) - ((B \ U).card : ℝ) ≤
          max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) := by
      have hle : ((A \ U).card : ℝ) ≤
          max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) :=
        le_max_left _ _
      linarith
    have h2 :
        -(((A \ U).card : ℝ) - ((B \ U).card : ℝ)) ≤
          max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) := by
      have hle : ((B \ U).card : ℝ) ≤
          max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) :=
        le_max_right _ _
      linarith
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hmax_le :
      max (((A \ U).card : ℝ)) (((B \ U).card : ℝ)) ≤
        max ((A.card : ℝ)) ((B.card : ℝ)) := by
    exact max_le_max (by exact_mod_cast hsdA) (by exact_mod_cast hsdB)
  have hcancel :
      ((U.card : ℝ) + ((A \ U).card : ℝ) -
          ((U.card : ℝ) + ((B \ U).card : ℝ))) =
        ((A \ U).card : ℝ) - ((B \ U).card : ℝ) := by
    ring
  rw [hcancel]
  exact le_trans h_abs hmax_le
