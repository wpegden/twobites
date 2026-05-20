import Tablet.TwoBiteEventProbability

-- [TABLET NODE: TwoBiteEventProbabilityTripleIntersectionLowerBound]

theorem TwoBiteEventProbabilityTripleIntersectionLowerBound :
    ∀ {n m : ℕ} {p : ℝ}
      (E F G : TwoBiteSample n m p → Prop),
      (∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω) →
      TwoBiteEventProbability n m p (fun _ => True) ≤ 1 →
      TwoBiteEventProbability n m p E +
          TwoBiteEventProbability n m p F +
            TwoBiteEventProbability n m p G - 2 ≤
        TwoBiteEventProbability n m p (fun ω => E ω ∧ F ω ∧ G ω) := by
-- BODY
  intro n m p E F G hweight htotal
  classical
  let Ω := TwoBiteSample n m p
  let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
  have hpoint :
      ∀ ω : Ω,
        (if E ω then w ω else 0) +
            (if F ω then w ω else 0) +
              (if G ω then w ω else 0) - 2 * w ω ≤
          (if E ω ∧ F ω ∧ G ω then w ω else 0) := by
    intro ω
    by_cases hE : E ω <;> by_cases hF : F ω <;> by_cases hG : G ω <;>
      simp [hE, hF, hG, w, hweight ω] <;> linarith [hweight ω]
  have hsum :
      (∑ ω : Ω,
        ((if E ω then w ω else 0) +
            (if F ω then w ω else 0) +
              (if G ω then w ω else 0) - 2 * w ω)) ≤
        ∑ ω : Ω, (if E ω ∧ F ω ∧ G ω then w ω else 0) := by
    exact Finset.sum_le_sum (by intro ω hω; exact hpoint ω)
  have hsum_rewrite :
      (∑ ω : Ω,
        ((if E ω then w ω else 0) +
            (if F ω then w ω else 0) +
              (if G ω then w ω else 0) - 2 * w ω)) =
        (∑ ω : Ω, if E ω then w ω else 0) +
          (∑ ω : Ω, if F ω then w ω else 0) +
            (∑ ω : Ω, if G ω then w ω else 0) -
              2 * (∑ ω : Ω, w ω) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.mul_sum]
  have htotal_sum : (∑ ω : Ω, w ω) ≤ 1 := by
    simpa [TwoBiteEventProbability, Ω, w] using htotal
  have hpre :
      (∑ ω : Ω, if E ω then w ω else 0) +
          (∑ ω : Ω, if F ω then w ω else 0) +
            (∑ ω : Ω, if G ω then w ω else 0) - 2 ≤
        (∑ ω : Ω, if E ω then w ω else 0) +
          (∑ ω : Ω, if F ω then w ω else 0) +
            (∑ ω : Ω, if G ω then w ω else 0) -
              2 * (∑ ω : Ω, w ω) := by
    nlinarith
  calc
    TwoBiteEventProbability n m p E +
        TwoBiteEventProbability n m p F +
          TwoBiteEventProbability n m p G - 2
        =
      (∑ ω : Ω, if E ω then w ω else 0) +
        (∑ ω : Ω, if F ω then w ω else 0) +
          (∑ ω : Ω, if G ω then w ω else 0) - 2 := by
            simp [TwoBiteEventProbability, Ω, w, Finset.sum_filter]
    _ ≤
      (∑ ω : Ω, if E ω then w ω else 0) +
        (∑ ω : Ω, if F ω then w ω else 0) +
          (∑ ω : Ω, if G ω then w ω else 0) -
            2 * (∑ ω : Ω, w ω) := hpre
    _ =
      (∑ ω : Ω,
        ((if E ω then w ω else 0) +
            (if F ω then w ω else 0) +
              (if G ω then w ω else 0) - 2 * w ω)) := by
            exact hsum_rewrite.symm
    _ ≤ ∑ ω : Ω, (if E ω ∧ F ω ∧ G ω then w ω else 0) := hsum
    _ = TwoBiteEventProbability n m p (fun ω => E ω ∧ F ω ∧ G ω) := by
      unfold TwoBiteEventProbability
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro ω hω
      by_cases h : E ω ∧ F ω ∧ G ω <;> simp [h, w]
