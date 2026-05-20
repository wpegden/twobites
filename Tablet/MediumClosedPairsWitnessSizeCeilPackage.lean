import Mathlib.Tactic
import Tablet.TwoBiteBaseVertex
import Tablet.TwoBiteLargeCutoff
import Tablet.TwoBiteSmallCutoff

-- [TABLET NODE: MediumClosedPairsWitnessSizeCeilPackage]

theorem MediumClosedPairsWitnessSizeCeilPackage
    {n m k : ℕ} {ε : ℝ}
    (hn_pos : 0 < (n : ℝ)) :
    let S : ℕ := Nat.ceil
      (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
          TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
    (∀ B : Finset (TwoBiteBaseVertex m),
      B.Nonempty →
      (B.card : ℝ) * TwoBiteSmallCutoff ε n
        ≤ (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
            TwoBiteLargeCutoff ε n →
      B.card ≤ S) ∧
    (S : ℝ) ≤
      (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) +
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) + 1 := by
-- BODY
  intro S
  have hsmall_pos : 0 < TwoBiteSmallCutoff ε n := by
    dsimp [TwoBiteSmallCutoff]
    exact Real.rpow_pos_of_pos hn_pos _
  have hquot_nonneg :
      0 ≤
        (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
          TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n) := by
    have hmain_nonneg :
        0 ≤ (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
      exact mul_nonneg (Nat.cast_nonneg k) (Real.rpow_pos_of_pos hn_pos _).le
    have hlarge_nonneg : 0 ≤ TwoBiteLargeCutoff ε n := by
      dsimp [TwoBiteLargeCutoff]
      exact (Real.rpow_pos_of_pos hn_pos _).le
    exact div_nonneg (add_nonneg hmain_nonneg hlarge_nonneg) hsmall_pos.le
  have hquot_eq :
      (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
          TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
        =
      (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) +
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
    dsimp [TwoBiteLargeCutoff, TwoBiteSmallCutoff]
    have hmain_div :
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
            Real.rpow (n : ℝ) (2 * ε) =
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) := by
      calc
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
            Real.rpow (n : ℝ) (2 * ε)
            = Real.rpow (n : ℝ) (((1 / 4 : ℝ) - ε) - 2 * ε) := by
              exact (Real.rpow_sub hn_pos ((1 / 4 : ℝ) - ε) (2 * ε)).symm
        _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) := by
              congr 1
              ring
    have hlarge_div :
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε) /
            Real.rpow (n : ℝ) (2 * ε) =
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
      calc
        Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε) /
            Real.rpow (n : ℝ) (2 * ε)
            = Real.rpow (n : ℝ) (((1 / 4 : ℝ) + ε) - 2 * ε) := by
              exact (Real.rpow_sub hn_pos ((1 / 4 : ℝ) + ε) (2 * ε)).symm
        _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
              congr 1
              ring
    calc
      ((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε)) /
          Real.rpow (n : ℝ) (2 * ε)
          =
        (k : ℝ) *
            (Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
              Real.rpow (n : ℝ) (2 * ε)) +
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) + ε) /
            Real.rpow (n : ℝ) (2 * ε) := by
            ring
      _ =
        (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) +
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) := by
            rw [hmain_div, hlarge_div]
  constructor
  · intro B _hBne hBsmall
    have hBreal :
        (B.card : ℝ) ≤
          (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
              TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n) := by
      rw [le_div_iff₀ hsmall_pos]
      simpa using hBsmall
    have hceil :
        (B.card : ℝ) ≤ (S : ℝ) := by
      let q :=
        (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
          TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n)
      have hceil_bound : q ≤ (S : ℝ) := by
        simpa [S, q] using Nat.le_ceil q
      exact le_trans hBreal hceil_bound
    exact Nat.cast_le.mp hceil
  · have hceil_lt :
        (S : ℝ) <
          (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
              TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n) + 1 := by
      simpa [S] using Nat.ceil_lt_add_one hquot_nonneg
    calc
      (S : ℝ) ≤
          (((k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) +
              TwoBiteLargeCutoff ε n) / TwoBiteSmallCutoff ε n) + 1 :=
            le_of_lt hceil_lt
      _ = (k : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) +
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) + 1 := by
            rw [hquot_eq]
