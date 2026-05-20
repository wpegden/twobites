import Tablet.WithHighProbability
import Tablet.NegligibleProbability
import Tablet.TwoBiteEventProbabilityTotalMassBound

-- [TABLET NODE: WithHighProbabilityOfNegligibleBadOnRegular]

theorem WithHighProbabilityOfNegligibleBadOnRegular :
    ∀ (m : ℕ → ℕ) (p : ℕ → ℝ)
      (Good R : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop),
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) →
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => ¬ Good n ω ∧ R n ω)) →
      (∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω) →
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (Good n)) := by
-- BODY
  intro m p Good R hR hBad hweight
  unfold WithHighProbability at hR ⊢
  unfold NegligibleProbability at hBad
  let r : ℕ → ℝ := fun n => TwoBiteEventProbability n (m n) (p n) (R n)
  let b : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (m n) (p n) (fun ω => ¬ Good n ω ∧ R n ω)
  let g : ℕ → ℝ := fun n => TwoBiteEventProbability n (m n) (p n) (Good n)
  have hr : Filter.Tendsto r Filter.atTop (nhds (1 : ℝ)) := by
    simpa [r] using hR
  have hb : Filter.Tendsto b Filter.atTop (nhds (0 : ℝ)) := by
    simpa [b] using hBad
  have hlower_tendsto :
      Filter.Tendsto (fun n => r n - b n) Filter.atTop (nhds (1 : ℝ)) := by
    have hsub := hr.sub hb
    convert hsub using 1
    norm_num
  have hlower :
      ∀ᶠ n in Filter.atTop, r n - b n ≤ g n := by
    filter_upwards [hweight] with n hnw
    classical
    let Ω := TwoBiteSample n (m n) (p n)
    let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
    have hpoint :
        ∀ ω : Ω,
          (if R n ω then w ω else 0) -
              (if ¬ Good n ω ∧ R n ω then w ω else 0) ≤
            (if Good n ω then w ω else 0) := by
      intro ω
      by_cases hGood : Good n ω <;> by_cases hRω : R n ω <;>
        simp [hGood, hRω, w, hnw ω]
    have hsum :
        (∑ ω : Ω,
          ((if R n ω then w ω else 0) -
            (if ¬ Good n ω ∧ R n ω then w ω else 0))) ≤
          ∑ ω : Ω, (if Good n ω then w ω else 0) := by
      exact Finset.sum_le_sum (by intro ω hω; exact hpoint ω)
    have hrewrite :
        (∑ ω : Ω,
          ((if R n ω then w ω else 0) -
            (if ¬ Good n ω ∧ R n ω then w ω else 0))) =
          (∑ ω : Ω, if R n ω then w ω else 0) -
            (∑ ω : Ω, if ¬ Good n ω ∧ R n ω then w ω else 0) := by
      rw [Finset.sum_sub_distrib]
    calc
      r n - b n =
          (∑ ω : Ω, if R n ω then w ω else 0) -
            (∑ ω : Ω, if ¬ Good n ω ∧ R n ω then w ω else 0) := by
            unfold r b TwoBiteEventProbability
            rw [Finset.sum_filter, Finset.sum_filter]
            refine congrArg₂ HSub.hSub rfl ?_
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases h : ¬ Good n ω ∧ R n ω <;> simp [h, w]
      _ = (∑ ω : Ω,
          ((if R n ω then w ω else 0) -
            (if ¬ Good n ω ∧ R n ω then w ω else 0))) := hrewrite.symm
      _ ≤ ∑ ω : Ω, (if Good n ω then w ω else 0) := hsum
      _ = g n := by
        unfold g TwoBiteEventProbability
        rw [Finset.sum_filter]
  have hupper :
      ∀ᶠ n in Filter.atTop, g n ≤ (fun _ : ℕ => (1 : ℝ)) n := by
    filter_upwards [hweight] with n hnw
    have hmono :
        TwoBiteEventProbability n (m n) (p n) (Good n) ≤
          TwoBiteEventProbability n (m n) (p n) (fun _ => True) := by
      classical
      unfold TwoBiteEventProbability
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by
          intro ω hω
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢)
        (by
          intro ω hωF hωnotE
          exact hnw ω)
    exact le_trans hmono (TwoBiteEventProbabilityTotalMassBound n (m n) (p n))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower_tendsto tendsto_const_nhds hlower hupper
