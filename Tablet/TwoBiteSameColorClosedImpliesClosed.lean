import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteXPlus
import Tablet.TwoBiteX
import Tablet.TwoBiteLiftedPositiveNeighborhood
import Tablet.TwoBiteLiftedNeighborhood
import Tablet.TwoBiteBasePairs

-- [TABLET NODE: TwoBiteSameColorClosedImpliesClosed]

theorem TwoBiteSameColorClosedImpliesClosed {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n))
    (e : Sum (Fin m × Fin m) (Fin m × Fin m)) :
    TwoBiteProjectionPairSameColorClosed ω I e →
      TwoBiteProjectionPairClosed ω I e := by
-- BODY
  classical
  intro h
  cases e with
  | inl q =>
      dsimp [TwoBiteProjectionPairSameColorClosed,
        TwoBiteProjectionPairClosed] at h ⊢
      rcases h with ⟨r, hq⟩
      refine ⟨Sum.inl r, ?_⟩
      have hsubset :
          (TwoBiteXPlus ω I (Sum.inl r)).image (TwoBiteRedProjection ω) ⊆
            (TwoBiteX ω I (Sum.inl r)).image (TwoBiteRedProjection ω) := by
        intro y hy
        rcases (Finset.mem_image.mp hy) with ⟨v, hv, hvproj⟩
        apply Finset.mem_image.mpr
        refine ⟨v, ?_, hvproj⟩
        simp [TwoBiteXPlus, TwoBiteX, TwoBiteLiftedPositiveNeighborhood,
          TwoBiteLiftedNeighborhood] at hv ⊢
        exact ⟨hv.1, hv.2.2⟩
      dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at hq ⊢
      rw [Finset.mem_filter] at hq ⊢
      rcases hq with ⟨hpairs, hrank⟩
      rw [Finset.mem_product] at hpairs ⊢
      exact ⟨⟨hsubset hpairs.1, hsubset hpairs.2⟩, hrank⟩
  | inr q =>
      dsimp [TwoBiteProjectionPairSameColorClosed,
        TwoBiteProjectionPairClosed] at h ⊢
      rcases h with ⟨b, hq⟩
      refine ⟨Sum.inr b, ?_⟩
      have hsubset :
          (TwoBiteXPlus ω I (Sum.inr b)).image (TwoBiteBlueProjection ω) ⊆
            (TwoBiteX ω I (Sum.inr b)).image (TwoBiteBlueProjection ω) := by
        intro y hy
        rcases (Finset.mem_image.mp hy) with ⟨v, hv, hvproj⟩
        apply Finset.mem_image.mpr
        refine ⟨v, ?_, hvproj⟩
        simp [TwoBiteXPlus, TwoBiteX, TwoBiteLiftedPositiveNeighborhood,
          TwoBiteLiftedNeighborhood] at hv ⊢
        exact ⟨hv.1, hv.2.2⟩
      dsimp [TwoBiteBasePairs, TwoBitePairsInSet] at hq ⊢
      rw [Finset.mem_filter] at hq ⊢
      rcases hq with ⟨hpairs, hrank⟩
      rw [Finset.mem_product] at hpairs ⊢
      exact ⟨⟨hsubset hpairs.1, hsubset hpairs.2⟩, hrank⟩
