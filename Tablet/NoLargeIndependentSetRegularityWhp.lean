import Tablet.FiberAndDegreeConcentration
import Tablet.MediumClosedPairsBound
import Tablet.SmallClosedPairsBound
import Tablet.TwoBiteRegularityEvent
import Tablet.ParameterHierarchy
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.WithHighProbability
import Tablet.WithHighProbabilityThreeIntersection
import Tablet.TwoBiteSampleWeightNonnegative

-- [TABLET NODE: NoLargeIndependentSetRegularityWhp]

theorem NoLargeIndependentSetRegularityWhp :
    ∀ (η ε1 ε2 β : ℝ) {n0 : ℕ},
      β = (1 / 2 : ℝ) →
      ParameterHierarchy η ε1 ε2 n0 →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              TwoBiteRegularityEvent
                (k := TwoBiteNaturalIndependenceScale (1 + η) n)
                η ε1 ε2 ω)) := by
-- BODY
  intro η ε1 ε2 β n0 hβ hHierarchy
  let m : ℕ → ℕ := fun n => TwoBiteNaturalReducedVertexCount n
  let k : ℕ → ℕ := fun n => TwoBiteNaturalIndependenceScale (1 + η) n
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let D : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun _ ω => FiberAndDegreeEvent ω ε2
  let M : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => TwoBiteMediumClosedPairsEvent (k := k n) η ε1 ω
  let S : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => TwoBiteSmallClosedPairsEvent (k := k n) η ε1 ω
  have hD :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (D n)) := by
    simpa [m, p, D] using
      FiberAndDegreeConcentration ε2 β hHierarchy.1 hβ m (by intro n; rfl)
  have hM :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (M n)) := by
    simpa [m, k, p, M] using
      MediumClosedPairsBound η ε1 ε2 β n0 m k hHierarchy hβ
        (by intro n; rfl) (by intro n; rfl)
  have hS :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (S n)) := by
    simpa [m, k, p, S] using
      SmallClosedPairsBound η ε1 ε2 β n0 m k hHierarchy hβ
        (by intro n; rfl) (by intro n; rfl)
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
  have hInter :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => D n ω ∧ M n ω ∧ S n ω)) :=
    WithHighProbabilityThreeIntersection m p D M S hD hM hS hweight
  simpa [m, k, p, D, M, S, TwoBiteRegularityEvent] using hInter
