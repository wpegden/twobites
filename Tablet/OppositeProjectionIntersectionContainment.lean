import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Tablet.Preamble

-- [TABLET NODE: OppositeProjectionIntersectionContainment]

theorem OppositeProjectionIntersectionContainment {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U V : Finset α) (f : α → β) :
    ((U.image f) ∩ (V.image f)).card ≤ (U ∩ V).card + ((V \ U).filter (fun v => f v ∈ (U \ V).image f)).card := by
-- BODY
  have h1 : U = (U ∩ V) ∪ (U \ V) := by ext x; simp; tauto
  have h2 : V = (U ∩ V) ∪ (V \ U) := by ext x; simp; tauto
  have h3 : U.image f = (U ∩ V).image f ∪ (U \ V).image f := by
    nth_rw 1 [h1]
    exact Finset.image_union _ _
  have h4 : V.image f = (U ∩ V).image f ∪ (V \ U).image f := by
    nth_rw 1 [h2]
    exact Finset.image_union _ _
  have h5 : U.image f ∩ V.image f = (U ∩ V).image f ∪ ((U \ V).image f ∩ (V \ U).image f) := by
    rw [h3, h4, Finset.union_inter_distrib_left]
  have h6 : ((V \ U).filter (fun v => f v ∈ (U \ V).image f)).image f = (U \ V).image f ∩ (V \ U).image f := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨v, ⟨hv1, hv2⟩, hvy⟩
      exact ⟨hvy ▸ hv2, ⟨v, hv1, hvy⟩⟩
    · rintro ⟨⟨u, hu, huy⟩, ⟨v, hv, hvy⟩⟩
      refine ⟨v, ⟨hv, ⟨u, hu, ?_⟩⟩, hvy⟩
      rw [huy, hvy]
  rw [h5, ←h6]
  refine (Finset.card_union_le _ _).trans ?_
  gcongr
  · exact Finset.card_image_le
  · exact Finset.card_image_le
