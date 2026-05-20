import Tablet.FixedSetHistoryCellBranchAveraging

-- [TABLET NODE: OppositeProjectionBlueExposureAveraging]

theorem OppositeProjectionBlueExposureAveraging {n m : ℕ} {p B : ℝ}
    (U₀ : Finset (Fin n)) (G_B : SimpleGraph (Fin m)) (ρ : Fin n → Fin m)
    (target : TwoBiteSample n m p → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hB : 0 ≤ B)
    (hbranch :
      ∀ η : U₀ → Fin m,
        TwoBiteEventProbability n m p
            (fun ω => target ω ∧
              (ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
                (fun u : U₀ => (ω.2.2 u.1).1) = η))
          ≤ B * TwoBiteEventProbability n m p
            (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ ∧
              (fun u : U₀ => (ω.2.2 u.1).1) = η)) :
    TwoBiteConditionalProbability n m p target
        (fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ) ≤ B := by
-- BODY
  classical
  let hist : TwoBiteSample n m p → Prop :=
    fun ω => ω.2.1 = G_B ∧ (fun v => (ω.2.2 v).2) = ρ
  let firstBranch : (U₀ → Fin m) → TwoBiteSample n m p → Prop :=
    fun η ω => hist ω ∧ (fun u : U₀ => (ω.2.2 u.1).1) = η
  have hbranch' :
      ∀ η : U₀ → Fin m,
        TwoBiteEventProbability n m p
            (fun ω => target ω ∧ hist ω ∧ firstBranch η ω)
          ≤ B * TwoBiteEventProbability n m p (firstBranch η) := by
    intro η
    simpa [hist, firstBranch, and_assoc, and_left_comm, and_comm] using hbranch η
  have havg :
      TwoBiteConditionalProbability n m p (fun ω => target ω ∧ hist ω) hist ≤ B := by
    refine
      @FixedSetHistoryCellBranchAveraging n m p B hist hist target (U₀ → Fin m) _
        firstBranch hp0 hp1 hB ?_ ?_ ?_ ?_ hbranch'
    · intro ω h
      exact h
    · intro η ω hη
      exact hη.1
    · intro ω hhist _hfixed
      refine ⟨fun u : U₀ => (ω.2.2 u.1).1, ?_⟩
      exact ⟨hhist, rfl⟩
    · intro η ζ hne ω hboth
      rcases hboth with ⟨hη, hζ⟩
      exact hne (hη.2.symm.trans hζ.2)
  simpa [TwoBiteConditionalProbability, hist, and_assoc, and_left_comm, and_comm] using havg
