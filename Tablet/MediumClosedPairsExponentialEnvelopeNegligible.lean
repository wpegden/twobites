import Mathlib.Tactic
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyBaseThreshold
import Tablet.ParameterHierarchyT28Threshold
import Tablet.ParameterHierarchyT28Algebra
import Tablet.ParameterHierarchyLogPositivity
import Tablet.TwoBiteNaturalIndependenceScale

open Filter
open scoped Topology

-- [TABLET NODE: MediumClosedPairsExponentialEnvelopeNegligible]

theorem MediumClosedPairsExponentialEnvelopeNegligible
    (ε ε1 ε2 : ℝ) (n0 : ℕ)
    (hparam : ParameterHierarchy ε ε1 ε2 n0) :
    Tendsto
      (fun n : ℕ =>
        Real.exp
          ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) * Real.log (n : ℝ) +
            2 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * Real.log (n : ℝ) -
            Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)))
      atTop (nhds (0 : ℝ)) := by
-- BODY
  rcases hparam with
    ⟨hε2_pos, hε2_lt_ε1, hε1_lt_ε, _hε_lt_one, hε_lt_sixteen,
      _hthree, _hsqrt, _hn0large, hcomp⟩
  have hε1_pos : 0 < ε1 := lt_trans hε2_pos hε2_lt_ε1
  have hε_pos : 0 < ε := lt_trans hε1_pos hε1_lt_ε
  obtain ⟨Nbase, hbase⟩ := ParameterHierarchyBaseThreshold ε hε_pos
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with n
    have hexp_pos :
        0 <
          Real.exp
            ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) * Real.log (n : ℝ) +
              2 * (TwoBiteNaturalIndependenceScale (1 + ε) n : ℝ) *
                Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * Real.log (n : ℝ) -
              Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) :=
      Real.exp_pos _
    linarith
  · intro b hb
    let δ : ℝ := b / 2
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      linarith
    have hδ_lt_b : δ < b := by
      dsimp [δ]
      linarith
    obtain ⟨N28, h28⟩ :=
      ParameterHierarchyT28Threshold ε δ hε_pos hδ_pos hε_lt_sixteen
    let N : ℕ := max n0 (max Nbase N28)
    filter_upwards [eventually_gt_atTop N] with n hn
    have hn0 : n0 < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
    have hnbase : Nbase < n := by
      exact lt_of_le_of_lt
        (le_trans (Nat.le_max_left Nbase N28) (Nat.le_max_right n0 (max Nbase N28))) hn
    have hn28 : N28 < n := by
      exact lt_of_le_of_lt
        (le_trans (Nat.le_max_right Nbase N28) (Nat.le_max_right n0 (max Nbase N28))) hn
    have hn_pos_nat : 0 < n := lt_of_le_of_lt (Nat.zero_le n0) hn0
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hL_pos : 0 < Real.log (n : ℝ) :=
      ParameterHierarchyLogPositivity hcomp hn0
    have hL_nonneg : 0 ≤ Real.log (n : ℝ) := le_of_lt hL_pos
    have hbase_n := hbase n hnbase
    dsimp at hbase_n
    rcases hbase_n with
      ⟨_hm_pos, _hp_base, _hp_le_half, _hpm, _hk_lower, _hk_succ, _hm_le,
        _hm_lt, _hK_le_n, hk_upper, _hloglog, _ht1⟩
    have h28_n := h28 n hn28
    dsimp at h28_n
    rcases h28_n with ⟨hfirst, hsecond, htail⟩
    let K := TwoBiteNaturalIndependenceScale (1 + ε) n
    let L := Real.log (n : ℝ)
    have hk_upper_alg :
        (K : ℝ) < 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L := by
      have hsqrt_mul :
          Real.sqrt ((n : ℝ) * L) = Real.sqrt (n : ℝ) * Real.sqrt L := by
        exact Real.sqrt_mul (Nat.cast_nonneg n) L
      calc
        (K : ℝ) < 2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := by
          simpa [K, L] using hk_upper
        _ = 2 * (1 + ε) * Real.sqrt (n : ℝ) * Real.sqrt L := by
          rw [hsqrt_mul]
          ring
    have hle_delta :
        Real.exp
          ((K : ℝ) * L +
            2 * (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε) * L -
            Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε)) ≤ δ := by
      simpa [K, L] using
        ParameterHierarchyT28Algebra ε δ (K : ℝ) n
          hn_pos (by simpa [L] using hL_nonneg) hk_upper_alg
          (by simpa [L] using hfirst)
          (by simpa [L] using hsecond)
          (by simpa [L] using htail)
    exact lt_of_le_of_lt (by simpa [K, L] using hle_delta) hδ_lt_b
