import Tablet.WithHighProbability
import Tablet.TwoBiteEventProbabilityTripleIntersectionLowerBound
import Tablet.TwoBiteEventProbabilityTotalMassBound

-- [TABLET NODE: WithHighProbabilityThreeIntersection]

theorem WithHighProbabilityThreeIntersection :
    ∀ (m : ℕ → ℕ) (p : ℕ → ℝ)
      (E F G : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop),
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (E n)) →
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (F n)) →
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (G n)) →
      (∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω) →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => E n ω ∧ F n ω ∧ G n ω)) := by
-- BODY
  intro m p E F G hE hF hG hweight
  unfold WithHighProbability at hE hF hG ⊢
  let a : ℕ → ℝ := fun n => TwoBiteEventProbability n (m n) (p n) (E n)
  let b : ℕ → ℝ := fun n => TwoBiteEventProbability n (m n) (p n) (F n)
  let c : ℕ → ℝ := fun n => TwoBiteEventProbability n (m n) (p n) (G n)
  let inter : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (m n) (p n)
      (fun ω => E n ω ∧ F n ω ∧ G n ω)
  have ha : Filter.Tendsto a Filter.atTop (nhds (1 : ℝ)) := by
    simpa [a] using hE
  have hb : Filter.Tendsto b Filter.atTop (nhds (1 : ℝ)) := by
    simpa [b] using hF
  have hc : Filter.Tendsto c Filter.atTop (nhds (1 : ℝ)) := by
    simpa [c] using hG
  have hlower :
      Filter.Tendsto (fun n => a n + b n + c n - 2)
        Filter.atTop (nhds (1 : ℝ)) := by
    have hsum : Filter.Tendsto (fun n => a n + b n + c n)
        Filter.atTop (nhds ((1 : ℝ) + 1 + 1)) :=
      (ha.add hb).add hc
    have htwo : Filter.Tendsto (fun _ : ℕ => (2 : ℝ))
        Filter.atTop (nhds (2 : ℝ)) :=
      tendsto_const_nhds
    have hsub := hsum.sub htwo
    convert hsub using 1
    norm_num
  have hle_lower :
      ∀ᶠ n in Filter.atTop, a n + b n + c n - 2 ≤ inter n := by
    filter_upwards [hweight] with n hnw
    exact TwoBiteEventProbabilityTripleIntersectionLowerBound
      (E n) (F n) (G n) hnw
      (TwoBiteEventProbabilityTotalMassBound n (m n) (p n))
  have prob_mono :
      ∀ {n : ℕ} {E F : TwoBiteSample n (m n) (p n) → Prop},
        (∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω) →
        (∀ ω, E ω → F ω) →
        TwoBiteEventProbability n (m n) (p n) E ≤
          TwoBiteEventProbability n (m n) (p n) F := by
    intro n E F hweight_n hEF
    classical
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω hωF hωnotE
        exact hweight_n ω)
  have hle_upper :
      ∀ᶠ n in Filter.atTop, inter n ≤ (fun _ : ℕ => (1 : ℝ)) n := by
    filter_upwards [hweight] with n hnw
    exact le_trans
      (prob_mono hnw (by intro ω hω; trivial))
      (TwoBiteEventProbabilityTotalMassBound n (m n) (p n))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds hle_lower hle_upper
