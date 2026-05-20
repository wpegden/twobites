import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Tablet.Preamble

-- [TABLET NODE: FixedSetTailExponentInequality]

lemma FixedSetTailExponentInequality {n m : ℕ} {C L ε r c t : ℝ}
    (hL : 0 < L)
    (hn : 0 < n)
    (hr : r = 2 * (m : ℝ))
    (hc : c = (1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε)))
    (ht : t = C / Real.sqrt L) :
    -(2 * t ^ 2) / (r * c ^ 2) ≤ -(C ^ 2 / (L * (m : ℝ) * ((n : ℝ) ^ (8 * ε)))) := by
-- BODY
  rw [hr, hc, ht]
  have h1 : (C / Real.sqrt L) ^ 2 = C ^ 2 / L := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hL)]
  have hn_pos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : (((n : ℝ) ^ (4 * ε)) ^ 2 : ℝ) = ((n : ℝ) ^ (8 * ε) : ℝ) := by
    have eq1 : (((n : ℝ) ^ (4 * ε)) ^ 2 : ℝ) = ((n : ℝ) ^ (4 * ε)) ^ (2 : ℝ) := by
      exact (Real.rpow_two _).symm
    rw [eq1]
    rw [← Real.rpow_mul hn_pos]
    have eq2 : (4 * ε) * 2 = 8 * ε := by ring
    rw [eq2]
  have h3 : ((1 / 2 : ℝ) * ((n : ℝ) ^ (4 * ε))) ^ 2 = (1 / 4 : ℝ) * ((n : ℝ) ^ (8 * ε)) := by
    rw [mul_pow, h2]
    norm_num
  rw [h1, h3]
  have h4 : -(2 * (C ^ 2 / L)) / (2 * (m : ℝ) * ((1 / 4 : ℝ) * ((n : ℝ) ^ (8 * ε)))) =
    - (4 * (C ^ 2 / (L * (m : ℝ) * ((n : ℝ) ^ (8 * ε))))) := by
    ring
  rw [h4]
  generalize hX : C ^ 2 / (L * (m : ℝ) * ((n : ℝ) ^ (8 * ε))) = X
  have hn_strict_pos : (0 : ℝ) < n := by exact Nat.cast_pos.mpr hn
  have h5 : 0 ≤ X := by
    rw [← hX]
    apply div_nonneg
    · positivity
    · apply mul_nonneg
      · apply mul_nonneg
        · exact le_of_lt hL
        · exact Nat.cast_nonneg m
      · exact Real.rpow_nonneg hn_pos _
  linarith
