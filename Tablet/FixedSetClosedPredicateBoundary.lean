import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBiteStageRevealedVertex
import Tablet.TwoBiteX
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteRedProjection
import Tablet.TwoBiteBlueProjection

-- [TABLET NODE: FixedSetClosedPredicateBoundary]

theorem FixedSetClosedPredicateBoundary :
    ∀ {n m : ℕ} {p ε : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (x : TwoBiteBaseVertex m),
      (∀ v : Fin n,
        v ∈ TwoBiteX ω I x ↔
          v ∈ I ∧ v ∈ TwoBiteLiftedNeighborhood ω x) ∧
      (∀ c : Sum (Fin m × Fin m) (Fin m × Fin m),
        TwoBiteStageRevealedVertex ω ε I x →
        (match x, c with
          | Sum.inl r, Sum.inl q => q.1 = r ∨ q.2 = r
          | Sum.inr b, Sum.inr q => q.1 = b ∨ q.2 = b
          | _, _ => False) →
        TwoBiteProjectionPairTouched ω ε I c) ∧
      (∀ q : Fin m × Fin m,
        q ∈
          TwoBiteBasePairs
            ((TwoBiteX ω I x).image (TwoBiteRedProjection ω)) →
        TwoBiteProjectionPairClosed ω I (Sum.inl q)) ∧
      (∀ q : Fin m × Fin m,
        q ∈
          TwoBiteBasePairs
            ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)) →
        TwoBiteProjectionPairClosed ω I (Sum.inr q)) := by
-- BODY
  classical
  intro n m p ε ω I x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    simp [TwoBiteX]
  · intro c hx hincident
    cases x with
    | inl r =>
        cases c with
        | inl q =>
            dsimp at hincident
            unfold TwoBiteProjectionPairTouched
            rcases hincident with hfirst | hsecond
            · left
              simpa [hfirst] using hx
            · right
              simpa [hsecond] using hx
        | inr q =>
            cases hincident
    | inr b =>
        cases c with
        | inl q =>
            cases hincident
        | inr q =>
            dsimp at hincident
            unfold TwoBiteProjectionPairTouched
            rcases hincident with hfirst | hsecond
            · left
              simpa [hfirst] using hx
            · right
              simpa [hsecond] using hx
  · intro q hq
    unfold TwoBiteProjectionPairClosed
    exact ⟨x, hq⟩
  · intro q hq
    unfold TwoBiteProjectionPairClosed
    exact ⟨x, hq⟩
