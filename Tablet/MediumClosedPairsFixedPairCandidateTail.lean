import Mathlib.Tactic
import Tablet.MediumClosedPairsFixedCandidateBinomialTail

-- [TABLET NODE: MediumClosedPairsFixedPairCandidateTail]

theorem MediumClosedPairsFixedPairCandidateTail
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (BR BB : Finset α) (PR PB : Finset β)
    (K : ℕ) (p A P : ℝ)
    (hp0 : 0 ≤ p)
    (hApos : 0 < A)
    (hPR : PR.card ≤ K)
    (hPB : PB.card ≤ K)
    (hmean :
      p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1))
    (hunion :
      P ≤
        (Nat.choose (BR.card * PR.card + BB.card * PB.card) ⌈A⌉₊ : ℝ) *
          p ^ ⌈A⌉₊) :
    P ≤ Real.exp (-A / 4) := by
-- BODY
  let N : ℕ := BR.card * PR.card + BB.card * PB.card
  have hred : BR.card * PR.card ≤ BR.card * K :=
    Nat.mul_le_mul_left BR.card hPR
  have hblue : BB.card * PB.card ≤ BB.card * K :=
    Nat.mul_le_mul_left BB.card hPB
  have hN_le : N ≤ (BR.card + BB.card) * K := by
    dsimp [N]
    calc
      BR.card * PR.card + BB.card * PB.card
          ≤ BR.card * K + BB.card * K := Nat.add_le_add hred hblue
      _ = (BR.card + BB.card) * K := by rw [Nat.add_mul]
  have hN_real_le :
      (N : ℝ) ≤ (((BR.card + BB.card) * K : ℕ) : ℝ) := by
    exact_mod_cast hN_le
  have hmeanN : p * (N : ℝ) ≤ A / (4 * Real.exp 1) := by
    have hmul :
        p * (N : ℝ) ≤ p * (((BR.card + BB.card) * K : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hN_real_le hp0
    exact le_trans hmul hmean
  simpa [N] using
    MediumClosedPairsFixedCandidateBinomialTail N p A P hp0 hApos hmeanN hunion
