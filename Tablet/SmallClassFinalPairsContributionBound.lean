import Tablet.TwoBiteSmallClass
import Tablet.FinalPairsCardLeHalfSq
import Mathlib.Tactic

-- [TABLET NODE: SmallClassFinalPairsContributionBound]

open scoped Classical

lemma SmallClassFinalPairsContributionBound {n m : ℕ} {p : ℝ}
    (ω : TwoBiteSample n m p) (I : Finset (Fin n)) (ε : ℝ)
    (x : TwoBiteBaseVertex m) (c_prod : ℝ)
    (hc_prod : c_prod = (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε)))
    (hxsmall : TwoBiteSmallClass ω ε I x) (pred : Fin n × Fin n → Prop) :
    (((TwoBiteFinalPairs (TwoBiteX ω I x)).filter pred).card : ℝ) ≤ c_prod := by
-- BODY
  classical
  have hfilter :
      (((TwoBiteFinalPairs (TwoBiteX ω I x)).filter pred).card : ℝ) ≤
        ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := by
    exact_mod_cast
      Finset.card_filter_le (s := TwoBiteFinalPairs (TwoBiteX ω I x)) (p := pred)
  have hfinal :
      ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) ≤
        ((TwoBiteX ω I x).card : ℝ) ^ 2 / 2 :=
    FinalPairsCardLeHalfSq (TwoBiteX ω I x)
  have hsmall : ((TwoBiteX ω I x).card : ℝ) ≤ TwoBiteSmallCutoff ε n := hxsmall.2
  have hnonneg : 0 ≤ ((TwoBiteX ω I x).card : ℝ) := by positivity
  have hsquare :
      ((TwoBiteX ω I x).card : ℝ) ^ 2 ≤ (TwoBiteSmallCutoff ε n) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg hsmall 2
  have hcut_sq :
      (TwoBiteSmallCutoff ε n) ^ 2 = ((n : ℝ) ^ (4 * ε)) := by
    dsimp [TwoBiteSmallCutoff]
    have hn : (0 : ℝ) ≤ n := by positivity
    calc
      ((n : ℝ) ^ (2 * ε)) ^ 2
          = ((n : ℝ) ^ (2 * ε)) ^ (2 : ℝ) := by
            exact (Real.rpow_natCast ((n : ℝ) ^ (2 * ε)) 2).symm
      _ = (n : ℝ) ^ ((2 * ε) * (2 : ℝ)) := by
            rw [← Real.rpow_mul hn]
      _ = (n : ℝ) ^ (4 * ε) := by
            ring_nf
  calc
    (((TwoBiteFinalPairs (TwoBiteX ω I x)).filter pred).card : ℝ)
        ≤ ((TwoBiteFinalPairs (TwoBiteX ω I x)).card : ℝ) := hfilter
    _ ≤ ((TwoBiteX ω I x).card : ℝ) ^ 2 / 2 := hfinal
    _ ≤ (TwoBiteSmallCutoff ε n) ^ 2 / 2 := by
          exact div_le_div_of_nonneg_right hsquare (by norm_num)
    _ = c_prod := by
          rw [hcut_sq, hc_prod]
          ring
