import Tablet.NoLargeIndependentSetRegularityWhp
import Tablet.FixedSetIndependenceProbability
import Tablet.NaturalIndependenceScaleFitsTarget
import Tablet.NaturalParameterApproximation
import Tablet.IndependenceNumberLess
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.WithHighProbability
import Tablet.NegligibleProbability
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.NoLargeIndependentSetBadRegularProbability

-- [TABLET NODE: NoLargeIndependentSetFromFixedSetBound]

theorem NoLargeIndependentSetFromFixedSetBound :
    ∀ (ε η ε1 ε2 β : ℝ) {n0 : ℕ},
      0 < ε →
      0 < η →
      η < ε →
      β = (1 / 2 : ℝ) →
      ParameterHierarchy η ε1 ε2 n0 →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              TwoBiteRegularityEvent
                (k := TwoBiteNaturalIndependenceScale (1 + η) n)
                η ε1 ε2 ω)) →
      (∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ,
          n0 ≤ N ∧
            ∀ {n m : ℕ} {p : ℝ} (I : Finset (Fin n)),
              N < n →
              m = TwoBiteNaturalReducedVertexCount n →
              p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
              I.card = TwoBiteNaturalIndependenceScale (1 + η) n →
              TwoBiteEventProbability n m p
                  (fun ω =>
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                      TwoBiteRegularityEvent (k := I.card) η ε1 ε2 ω)
                ≤ δ * ((Nat.choose n I.card : ℝ)⁻¹)) →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))))) := by
-- BODY
  intro ε η ε1 ε2 β n0 hε hη hη_lt hβ hHierarchy hRegular hFixed
  let m : ℕ → ℕ := fun n => TwoBiteNaturalReducedVertexCount n
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
        ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)))
  let R : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      TwoBiteRegularityEvent
        (k := TwoBiteNaturalIndependenceScale (1 + η) n)
        η ε1 ε2 ω
  have hR :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) := by
    simpa [m, p, R] using hRegular
  have hBad :
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => ¬ Good n ω ∧ R n ω)) := by
    simpa [m, p, Good, R] using
      NoLargeIndependentSetBadRegularProbability ε η ε1 ε2 β
        hε hη hη_lt hβ hHierarchy hFixed
  have hHierarchyCopy := hHierarchy
  rcases hHierarchyCopy with
    ⟨hε2_pos, hε2_lt, hε1_lt, hη_lt_one, hη_lt_sixteen, hthree,
      height, hn0sq, hEventually⟩
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [Filter.eventually_gt_atTop n0] with n hn
    intro ω
    have hcomp := hEventually n hn
    dsimp only at hcomp
    rcases hcomp with ⟨hm_pos, hp_nonneg, hp_le_half, hrest⟩
    have hp_nonneg' : 0 ≤ TwoBiteEdgeProbability β n := by
      simpa [hβ, TwoBiteEdgeProbability] using hp_nonneg
    have hp_le_one' : TwoBiteEdgeProbability β n ≤ 1 := by
      have hp_le_half' : TwoBiteEdgeProbability β n ≤ (1 / 2 : ℝ) := by
        simpa [hβ, TwoBiteEdgeProbability] using hp_le_half
      linarith
    simpa [m, p] using TwoBiteSampleWeightNonnegative ω hp_nonneg' hp_le_one'
  have hGood :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    WithHighProbabilityOfNegligibleBadOnRegular m p Good R hR hBad hweight
  simpa [m, p, Good] using hGood
