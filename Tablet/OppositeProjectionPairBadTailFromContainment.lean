import Tablet.OppositeProjectionIntersectionContainment
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic

-- [TABLET NODE: OppositeProjectionPairBadTailFromContainment]

theorem OppositeProjectionPairBadTailFromContainment {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (U V U₀ : Finset α) (f : α → β) (η : U₀ → β) (τ : ℝ)
    (hU₀ : U₀ = U \ V)
    (hη : ∀ u : U₀, f u.1 = η u)
    (hbad :
      (((U.image f ∩ V.image f).card : ℝ) > ((U ∩ V).card : ℝ) + τ)) :
    Nat.ceil τ ≤ ((V \ U).filter (fun v => f v ∈ Finset.univ.image η)).card := by
-- BODY
  classical
  let inner : Finset α := (V \ U).filter (fun v => f v ∈ (U \ V).image f)
  let tail : Finset α := (V \ U).filter (fun v => f v ∈ Finset.univ.image η)
  have hinner_tail : inner.card ≤ tail.card := by
    apply Finset.card_le_card
    intro v hv
    simp only [inner, tail, Finset.mem_filter] at hv ⊢
    rcases hv with ⟨hvVU, hvimg⟩
    rcases Finset.mem_image.mp hvimg with ⟨u, huUV, hfu⟩
    have huU₀ : u ∈ U₀ := by
      rwa [hU₀]
    refine ⟨hvVU, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨u, huU₀⟩, Finset.mem_univ _, ?_⟩
    exact (hη ⟨u, huU₀⟩).symm.trans hfu
  have hcontain_real :
      ((U.image f ∩ V.image f).card : ℝ) ≤ ((U ∩ V).card : ℝ) + (inner.card : ℝ) := by
    have hcontain := OppositeProjectionIntersectionContainment U V f
    exact_mod_cast (by simpa [inner] using hcontain)
  have htail_real : (inner.card : ℝ) ≤ (tail.card : ℝ) := by
    exact_mod_cast hinner_tail
  have htau : τ ≤ (tail.card : ℝ) := by
    linarith
  simpa [tail] using (Nat.ceil_le).2 htau
