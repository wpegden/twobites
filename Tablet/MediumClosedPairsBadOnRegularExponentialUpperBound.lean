import Mathlib.Tactic
import Tablet.FiberAndDegreeEvent
import Tablet.MediumClosedPairsFiniteCandidateUnionBound
import Tablet.TwoBiteEventProbabilitySumOverEmbeddings
import Tablet.TwoBiteMediumClosedPairsEvent

-- [TABLET NODE: MediumClosedPairsBadOnRegularExponentialUpperBound]

theorem MediumClosedPairsBadOnRegularExponentialUpperBound
    {n m k : ℕ} {p ε ε1 ε2 countExp tailExp : ℝ}
    {ι : Type} [Fintype ι]
    (Candidate : ι → TwoBiteSample n m p → Prop)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcover :
      ∀ ω : TwoBiteSample n m p,
        (¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
          FiberAndDegreeEvent ω ε2) →
          ∃ i : ι, Candidate i ω)
    (hcell_tail :
      ∀ i : ι, ∀ π : Fin n ↪ (Fin m × Fin m),
        TwoBiteEventProbability n m p
          (fun ω => TwoBiteEmbedding ω = π ∧ Candidate i ω)
        ≤
          Real.exp (-tailExp) *
            TwoBiteEventProbability n m p
              (fun ω => TwoBiteEmbedding ω = π))
    (hcard : (Fintype.card ι : ℝ) ≤ Real.exp countExp) :
    TwoBiteEventProbability n m p
      (fun ω =>
        ¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
          FiberAndDegreeEvent ω ε2)
      ≤ Real.exp (countExp - tailExp) := by
-- BODY
  classical
  let Bad : TwoBiteSample n m p → Prop :=
    fun ω =>
      ¬ TwoBiteMediumClosedPairsEvent (k := k) ε ε1 ω ∧
        FiberAndDegreeEvent ω ε2
  have htail :
      ∀ i : ι,
        TwoBiteEventProbability n m p (Candidate i) ≤ Real.exp (-tailExp) := by
    intro i
    exact
      TwoBiteEventProbabilitySumOverEmbeddings
        (Candidate i) (Real.exp (-tailExp)) (hcell_tail i)
        (le_of_lt (Real.exp_pos _))
  have hfinite :
      TwoBiteEventProbability n m p Bad ≤
        (Fintype.card ι : ℝ) * Real.exp (-tailExp) := by
    exact
      MediumClosedPairsFiniteCandidateUnionBound
        Bad Candidate hp0 hp1
        (by
          intro ω hω
          exact hcover ω hω)
        htail
  have htail_nonneg : 0 ≤ Real.exp (-tailExp) :=
    le_of_lt (Real.exp_pos _)
  have hprod_bound :
      (Fintype.card ι : ℝ) * Real.exp (-tailExp) ≤
        Real.exp countExp * Real.exp (-tailExp) :=
    mul_le_mul_of_nonneg_right hcard htail_nonneg
  have hexp :
      Real.exp countExp * Real.exp (-tailExp) =
        Real.exp (countExp - tailExp) := by
    rw [← Real.exp_add]
    ring_nf
  exact le_trans (by simpa [Bad] using hfinite) (by simpa [hexp] using hprod_bound)
