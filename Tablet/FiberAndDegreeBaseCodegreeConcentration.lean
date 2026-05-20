import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteSampleWeight
import Tablet.TwoBiteSampleWeightNonnegative
import Tablet.UniformInjectionWeight
import Tablet.TwoBiteEdgeProbability
import Tablet.OppositeProjectionEdgeProbBounds
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.TwoBiteReducedVertexCount
import Tablet.TwoBiteStretch
import Tablet.TwoBiteNaturalTotalMassOneEventually
import Tablet.TwoBiteSample
import Tablet.WithHighProbability
import Tablet.TwoBiteRedGraph
import Tablet.TwoBiteBlueGraph
import Tablet.GnpGraphWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.NegligibleProbability
import Tablet.WithHighProbabilityOfNegligibleBadOnRegular
import Tablet.FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible

open Filter

-- [TABLET NODE: FiberAndDegreeBaseCodegreeConcentration]

open Classical in
theorem FiberAndDegreeBaseCodegreeConcentration :
    ∀ β : ℝ, β = (1 / 2 : ℝ) →
      ∀ m : ℕ → ℕ,
        (∀ n : ℕ, m n = TwoBiteNaturalReducedVertexCount n) →
        WithHighProbability
          (fun n =>
            TwoBiteEventProbability n (m n) (TwoBiteEdgeProbability β n)
              (fun ω =>
                (∀ r s : Fin (m n), r ≠ s →
                  ((Finset.univ.filter (fun t : Fin (m n) => (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)) ∧
                (∀ b c : Fin (m n), b ≠ c →
                  ((Finset.univ.filter (fun t : Fin (m n) => (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤ 100 * Real.log (n : ℝ)))) := by
-- BODY
  intro β hβ m hm
  classical
  let p : ℕ → ℝ := fun n => TwoBiteEdgeProbability β n
  let SharpGood : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((Finset.univ.filter
          (fun t : Fin (m n) =>
            (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤
          Real.log (n : ℝ)) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((Finset.univ.filter
          (fun t : Fin (m n) =>
            (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤
          Real.log (n : ℝ))
  let Good : ∀ n : ℕ, TwoBiteSample n (m n) (p n) → Prop :=
    fun n ω =>
      (∀ r s : Fin (m n), r ≠ s →
        ((Finset.univ.filter
          (fun t : Fin (m n) =>
            (TwoBiteRedGraph ω).Adj r t ∧ (TwoBiteRedGraph ω).Adj s t)).card : ℝ) ≤
          100 * Real.log (n : ℝ)) ∧
      (∀ b c : Fin (m n), b ≠ c →
        ((Finset.univ.filter
          (fun t : Fin (m n) =>
            (TwoBiteBlueGraph ω).Adj b t ∧ (TwoBiteBlueGraph ω).Adj c t)).card : ℝ) ≤
          100 * Real.log (n : ℝ))
  have hpBounds : ∀ᶠ n in Filter.atTop, 0 ≤ p n ∧ p n ≤ 1 := by
    filter_upwards [OppositeProjectionEdgeProbBounds] with n hn
    simpa [p, hβ] using hn
  have hlogNonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hSharpBad :
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ SharpGood n ω)) := by
    simpa [p, SharpGood] using
      FiberAndDegreeSameColorBaseCodegreeSharpFailureNegligible β hβ m hm
  let badProb : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (m n) (p n)
      (fun ω => ¬ Good n ω ∧ True)
  let sharpBadProb : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (m n) (p n)
      (fun ω => ¬ SharpGood n ω)
  have hSharpBadTendsto :
      Filter.Tendsto sharpBadProb Filter.atTop (nhds (0 : ℝ)) := by
    simpa [NegligibleProbability, sharpBadProb] using hSharpBad
  have hBadLower :
      ∀ᶠ n in Filter.atTop, (fun _ : ℕ => (0 : ℝ)) n ≤ badProb n := by
    filter_upwards [hpBounds] with n hp
    dsimp [badProb]
    exact TwoBiteEventProbabilityNonnegative hp.1 hp.2 _
  have hBadUpper :
      ∀ᶠ n in Filter.atTop, badProb n ≤ sharpBadProb n := by
    filter_upwards [hpBounds, hlogNonneg] with n hp hlog
    dsimp [badProb, sharpBadProb]
    unfold TwoBiteEventProbability
    refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      rcases hω with ⟨hnotGood, _⟩
      intro hSharp
      apply hnotGood
      rcases hSharp with ⟨hRed, hBlue⟩
      constructor
      · intro r s hrs
        have hbase := hRed r s hrs
        exact le_trans hbase (by nlinarith)
      · intro b c hbc
        have hbase := hBlue b c hbc
        exact le_trans hbase (by nlinarith)
    · intro ω _ _
      exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  have hBadTendsto :
      Filter.Tendsto badProb Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hSharpBadTendsto hBadLower hBadUpper
  have hTrue :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (fun _ => True)) := by
    unfold WithHighProbability
    have htotal := TwoBiteNaturalTotalMassOneEventually β hβ m hm
    have hEq :
        (fun _ : ℕ => (1 : ℝ)) =ᶠ[Filter.atTop]
          (fun n =>
            TwoBiteEventProbability n (m n) (p n) (fun _ => True)) := by
      filter_upwards [htotal] with n hn
      simpa [p] using hn.2.symm
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hBad :
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n)
            (fun ω => ¬ Good n ω ∧ True)) := by
    simpa [NegligibleProbability, badProb] using hBadTendsto
  have hweight :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (m n) (p n), 0 ≤ TwoBiteSampleWeight ω := by
    filter_upwards [hpBounds] with n hp ω
    exact TwoBiteSampleWeightNonnegative ω hp.1 hp.2
  have hGood :
      WithHighProbability
        (fun n =>
          TwoBiteEventProbability n (m n) (p n) (Good n)) :=
    WithHighProbabilityOfNegligibleBadOnRegular
      m p Good (fun _ _ => True) hTrue hBad hweight
  simpa [Good, p] using hGood
