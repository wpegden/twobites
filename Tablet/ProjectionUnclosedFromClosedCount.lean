import Mathlib.Tactic.Linarith
import Tablet.TwoBiteUnclosedProjectedPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed

-- [TABLET NODE: ProjectionUnclosedFromClosedCount]

theorem ProjectionUnclosedFromClosedCount :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (f err : ℝ),
      ((@Finset.filter (Sum (Fin m × Fin m) (Fin m × Fin m))
          (fun e => TwoBiteProjectionPairClosed ω I e)
          (Classical.decPred (fun e => TwoBiteProjectionPairClosed ω I e))
          (TwoBiteProjectionPairSet ω I)).card : ℝ) ≤
        ((TwoBiteProjectionPairSet ω I).card : ℝ) - f + err →
      f - err ≤ ((TwoBiteUnclosedProjectedPairs ω I).card : ℝ) := by
-- BODY
  intro n m p ω I f err hclosed
  classical
  let P := TwoBiteProjectionPairSet ω I
  let closed : Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e => TwoBiteProjectionPairClosed ω I e
  have hcardNat :
      (P.filter closed).card + (P.filter (fun e => ¬ closed e)).card = P.card := by
    simpa [P, closed] using
      (Finset.card_filter_add_card_filter_not (s := P) (p := closed))
  have hcardReal :
      ((P.filter (fun e => ¬ closed e)).card : ℝ) =
        (P.card : ℝ) - ((P.filter closed).card : ℝ) := by
    have hcast :
        (((P.filter closed).card + (P.filter (fun e => ¬ closed e)).card : ℕ) : ℝ) =
          (P.card : ℝ) := by
      exact_mod_cast hcardNat
    norm_num at hcast ⊢
    nlinarith
  have hunclosed :
      ((TwoBiteUnclosedProjectedPairs ω I).card : ℝ) =
        ((P.filter (fun e => ¬ closed e)).card : ℝ) := by
    simp [TwoBiteUnclosedProjectedPairs, P, closed]
  have hclosed' :
      (((P.filter closed).card : ℝ) ≤ (P.card : ℝ) - f + err) := by
    simpa [P, closed] using hclosed
  rw [hunclosed, hcardReal]
  nlinarith
