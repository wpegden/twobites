import Tablet.NegligibleProbability
import Tablet.WithHighProbability
import Tablet.RealChooseTwo
import Tablet.BoundedDifferencesProduct
import Tablet.FiberAndDegreeConcentration
import Tablet.FiberAndDegreeEvent
import Tablet.SmallClosedPairsBadEventProbability
import Tablet.SmallClosedPairsFixedSetTail
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyEventualComparisons
import Tablet.ClosedPairsBound
import Tablet.TwoBiteClosedPairsInClass
import Tablet.TwoBiteSmallClosedPairsEvent
import Tablet.TwoBiteSmallClass
import Tablet.TwoBiteSmallCutoff
import Tablet.TwoBiteX
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEventProbabilityNonnegative
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular

-- [TABLET NODE: SmallClosedPairsBound]

theorem SmallClosedPairsBound :
    ∀ (ε ε1 ε2 β : ℝ) (n0 : ℕ) (m k : ℕ → ℕ),
      ParameterHierarchy ε ε1 ε2 n0 →
      β = (1 / 2 : ℝ) →
      (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
      (∀ n : ℕ, k n = TwoBiteNaturalIndependenceScale (1 + ε) n) →
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
            (fun ω => TwoBiteSmallClosedPairsEvent (k := k n) ε ε1 ω)) := by
-- BODY
  classical
  intro ε ε1 ε2 β n0 m k hHierarchy hβ hm hk
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => TwoBiteSmallClosedPairsEvent (k := k n) ε ε1 ω
  let R : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω => FiberAndDegreeEvent ω ε2
  have hHierarchyCopy := hHierarchy
  rcases hHierarchyCopy with
    ⟨hε2_pos, _, _, _, _, _, _, _, hEventually⟩
  have hR :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (R n)) := by
    simpa [p, R] using FiberAndDegreeConcentration ε2 β hε2_pos hβ m hm
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [Filter.eventually_gt_atTop n0] with n hn
    intro ω
    have hcomp := hEventually n hn
    dsimp only at hcomp
    rcases hcomp with ⟨_, hp_nonneg, hp_le_half, _⟩
    have hp_nonneg' : 0 ≤ TwoBiteEdgeProbability β n := by
      simpa [hβ, TwoBiteEdgeProbability] using hp_nonneg
    have hp_le_one' : TwoBiteEdgeProbability β n ≤ 1 := by
      have hp_le_half' : TwoBiteEdgeProbability β n ≤ (1 / 2 : ℝ) := by
        simpa [hβ, TwoBiteEdgeProbability] using hp_le_half
      exact le_trans hp_le_half' (by norm_num)
    simpa [p] using TwoBiteSampleWeightNonnegative ω hp_nonneg' hp_le_one'
  have hBad :
      NegligibleProbability
        (fun n => TwoBiteEventProbability n (m n) (p n)
          (fun ω => ¬ Good n ω ∧ R n ω)) := by
    unfold NegligibleProbability
    have hinv :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹)
          Filter.atTop (nhds (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    have h_nonneg :
        ∀ᶠ n in Filter.atTop,
          0 ≤ TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ R n ω) := by
      filter_upwards [Filter.eventually_gt_atTop n0] with n hn
      have hcomp := hEventually n hn
      dsimp only at hcomp
      rcases hcomp with ⟨_, hp_nonneg, hp_le_half, _⟩
      have hp_nonneg' : 0 ≤ TwoBiteEdgeProbability β n := by
        simpa [hβ, TwoBiteEdgeProbability] using hp_nonneg
      have hp_le_one' : TwoBiteEdgeProbability β n ≤ 1 := by
        have hp_le_half' : TwoBiteEdgeProbability β n ≤ (1 / 2 : ℝ) := by
          simpa [hβ, TwoBiteEdgeProbability] using hp_le_half
        exact le_trans hp_le_half' (by norm_num)
      simpa [p] using
        TwoBiteEventProbabilityNonnegative hp_nonneg' hp_le_one'
          (fun ω : TwoBiteSample n (m n) (p n) => ¬ Good n ω ∧ R n ω)
    have h_bound :
        ∀ᶠ n in Filter.atTop,
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ R n ω) ≤ (n : ℝ)⁻¹ := by
      filter_upwards [Filter.eventually_gt_atTop n0] with n hn
      have hbad :=
        SmallClosedPairsBadEventProbability
          ε ε1 ε2 β (n0 := n0) (n := n) (m := m n) (k := k n)
          hHierarchy hβ hn (hm n) (hk n)
      simpa [p, Good, R, and_comm] using hbad
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hinv h_nonneg h_bound
  have hGood :
      WithHighProbability
        (fun n => TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    WithHighProbabilityOfNegligibleBadOnRegular m p Good R hR hBad hweight
  simpa [p, Good] using hGood
