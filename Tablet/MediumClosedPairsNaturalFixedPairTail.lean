import Mathlib.Tactic
import Tablet.MediumClosedPairsFixedPairCandidateTail
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: MediumClosedPairsNaturalFixedPairTail]

theorem MediumClosedPairsNaturalFixedPairTail
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (ε : ℝ) (n : ℕ)
    (BR BB : Finset α) (PR PB : Finset β)
    (P : ℝ) :
    let K := TwoBiteNaturalIndependenceScale (1 + ε) n
    let p := TwoBiteEdgeProbability (1 / 2 : ℝ) n
    let A := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
      (6 * (Real.log (n : ℝ)) ^ 2)
    0 < A →
    0 ≤ p →
    PR.card ≤ K →
    PB.card ≤ K →
    p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1) →
    Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) ≤ A / 4 →
    P ≤
      (Nat.choose (BR.card * PR.card + BB.card * PB.card) ⌈A⌉₊ : ℝ) *
        p ^ ⌈A⌉₊ →
    P ≤ Real.exp (-(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε))) := by
-- BODY
  intro K p A hApos hp0 hPR hPB hmean hAnat hunion
  have hfixed :
      P ≤ Real.exp (-A / 4) :=
    MediumClosedPairsFixedPairCandidateTail BR BB PR PB K p A P
      hp0 hApos hPR hPB hmean hunion
  have hexponent :
      -A / 4 ≤ -(Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) := by
    linarith
  exact le_trans hfixed (Real.exp_le_exp.mpr hexponent)
