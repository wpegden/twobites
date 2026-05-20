import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Tablet.MediumClosedPairsCoordinateUnionBridge

-- [TABLET NODE: MediumClosedPairsNormalizedCoordinateUnionBridge]

open scoped BigOperators

theorem MediumClosedPairsNormalizedCoordinateUnionBridge
    {n m t : ℕ} {p : ℝ}
    (BR BB PR PB : Finset (Fin m))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let normalize : Fin m × Fin m → Fin m × Fin m :=
      fun e => if e.1.val < e.2.val then e else (e.2, e.1)
    let redRaw : Finset (Fin m × Fin m) :=
      (BR.product PR).filter (fun e => e.1 ≠ e.2)
    let blueRaw : Finset (Fin m × Fin m) :=
      (BB.product PB).filter (fun e => e.1 ≠ e.2)
    let C : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
      redRaw.image
          (fun e => (Sum.inl (normalize e) :
            Sum (Fin m × Fin m) (Fin m × Fin m))) ∪
        blueRaw.image
          (fun e => (Sum.inr (normalize e) :
            Sum (Fin m × Fin m) (Fin m × Fin m)))
    (∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
      A ∈ C.powersetCard t →
        TwoBiteEventProbability n m p
          (fun ω => ∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e) ≤
            p ^ t) →
    TwoBiteEventProbability n m p
      (fun ω =>
        t ≤
          (@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
            (fun e => TwoBiteEdgeCoordinateValue ω e)
            (Classical.decPred _) C).card)
      ≤
        (Nat.choose (BR.card * PR.card + BB.card * PB.card) t : ℝ) *
          p ^ t := by
-- BODY
  classical
  intro normalize redRaw blueRaw C hfixed
  have hredRaw_card : redRaw.card ≤ (BR.product PR).card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hblueRaw_card : blueRaw.card ≤ (BB.product PB).card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hredImage_card :
      (redRaw.image
        (fun e => (Sum.inl (normalize e) :
          Sum (Fin m × Fin m) (Fin m × Fin m)))).card ≤ redRaw.card :=
    Finset.card_image_le
  have hblueImage_card :
      (blueRaw.image
        (fun e => (Sum.inr (normalize e) :
          Sum (Fin m × Fin m) (Fin m × Fin m)))).card ≤ blueRaw.card :=
    Finset.card_image_le
  have hCcard :
      C.card ≤ BR.card * PR.card + BB.card * PB.card := by
    calc
      C.card
          ≤ (redRaw.image
                (fun e => (Sum.inl (normalize e) :
                  Sum (Fin m × Fin m) (Fin m × Fin m)))).card +
              (blueRaw.image
                (fun e => (Sum.inr (normalize e) :
                  Sum (Fin m × Fin m) (Fin m × Fin m)))).card := by
            simpa [C] using
              Finset.card_union_le
                (redRaw.image
                  (fun e => (Sum.inl (normalize e) :
                    Sum (Fin m × Fin m) (Fin m × Fin m))))
                (blueRaw.image
                  (fun e => (Sum.inr (normalize e) :
                    Sum (Fin m × Fin m) (Fin m × Fin m))))
      _ ≤ redRaw.card + blueRaw.card := Nat.add_le_add hredImage_card hblueImage_card
      _ ≤ (BR.product PR).card + (BB.product PB).card :=
            Nat.add_le_add hredRaw_card hblueRaw_card
      _ = BR.card * PR.card + BB.card * PB.card := by simp
  exact
    MediumClosedPairsCoordinateUnionBridge
      (n := n) (m := m) (t := t)
      (N := BR.card * PR.card + BB.card * PB.card)
      (p := p) C hp0 hp1 hCcard hfixed
