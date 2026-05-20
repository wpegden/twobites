import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Tablet.MediumClosedPairsCompressedTailAbsorptions
import Tablet.MediumClosedPairsNaturalTailHypotheses
import Tablet.ParameterHierarchy
import Tablet.ParameterHierarchyBaseThreshold
import Tablet.ParameterHierarchyT28Threshold
import Tablet.ParameterHierarchyLogPositivity

open Filter
open scoped Topology

set_option maxHeartbeats 800000

-- [TABLET NODE: MediumClosedPairsHierarchyTailInputs]

theorem MediumClosedPairsHierarchyTailInputs
    {α : Type} [DecidableEq α]
    (ε ε1 ε2 : ℝ) (n0 : ℕ)
    (hparam : ParameterHierarchy ε ε1 ε2 n0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ BR BB : Finset α,
        let K := TwoBiteNaturalIndependenceScale (1 + ε) n
        let p := TwoBiteEdgeProbability (1 / 2 : ℝ) n
        let A := (K : ℝ) * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - ε) /
          (6 * (Real.log (n : ℝ)) ^ 2)
        ((BR.card + BB.card : ℝ) ≤
          (3 / 2 : ℝ) * (K : ℝ) *
            Real.rpow (n : ℝ) ((1 / 4 : ℝ) - 3 * ε)) →
        0 < A ∧
          0 ≤ p ∧
          p * (((BR.card + BB.card) * K : ℕ) : ℝ) ≤ A / (4 * Real.exp 1) ∧
          Real.rpow (n : ℝ) ((3 / 4 : ℝ) - 2 * ε) ≤ A / 4 := by
-- BODY
  rcases hparam with
    ⟨hε2_pos, hε2_lt_ε1, hε1_lt_ε, hε_lt_one, hε_lt_sixteen,
      _hthree, _hsqrt, _hn0large, hcomp⟩
  have hε1_pos : 0 < ε1 := lt_trans hε2_pos hε2_lt_ε1
  have hε_pos : 0 < ε := lt_trans hε1_pos hε1_lt_ε
  obtain ⟨Nbase, hbase⟩ := ParameterHierarchyBaseThreshold ε hε_pos
  obtain ⟨N28, h28⟩ :=
    ParameterHierarchyT28Threshold ε ε1 hε_pos hε1_pos hε_lt_sixteen
  let N : ℕ := max n0 (max Nbase N28)
  filter_upwards [eventually_gt_atTop N,
    MediumClosedPairsCompressedTailAbsorptions ε hε_pos] with n hn hcompressed
  intro BR BB
  dsimp
  intro hsize
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
    ⟨_hm_pos, _hp_base, _hp_le_half, _hpm, hk_lower, _hk_succ, _hm_le,
      _hm_lt, _hK_le_n, hk_upper, _hloglog, _ht1⟩
  have h28_n := h28 n hn28
  dsimp at h28_n
  rcases h28_n with ⟨_hfirst, hsecond, _htail_exp⟩
  let K := TwoBiteNaturalIndependenceScale (1 + ε) n
  let p := TwoBiteEdgeProbability (1 / 2 : ℝ) n
  let L := Real.log (n : ℝ)
  let epow := Real.rpow (n : ℝ) ε
  have hp_nonneg : 0 ≤ p := by
    dsimp [p, TwoBiteEdgeProbability]
    positivity
  have hpK : p * (K : ℝ) ≤ (1 + ε) * L := by
    have hK_upper_le : (K : ℝ) ≤ 2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L)) := by
      exact le_of_lt (by simpa [K, L] using hk_upper)
    have hp_formula : p = (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) := by
      dsimp [p, L, TwoBiteEdgeProbability]
    have hsqrt_product :
        Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) = L := by
      have hdiv_nonneg : 0 ≤ L / (n : ℝ) :=
        div_nonneg (by simpa [L] using hL_nonneg) hn_pos.le
      have harg_eq : (L / (n : ℝ)) * ((n : ℝ) * L) = L ^ 2 := by
        field_simp [ne_of_gt hn_pos]
      calc
        Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L) =
            Real.sqrt ((L / (n : ℝ)) * ((n : ℝ) * L)) := by
          rw [Real.sqrt_mul hdiv_nonneg]
        _ = Real.sqrt (L ^ 2) := by rw [harg_eq]
        _ = |L| := Real.sqrt_sq_eq_abs L
        _ = L := abs_of_nonneg (by simpa [L] using hL_nonneg)
    calc
      p * (K : ℝ)
          ≤ p * (2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L))) := by
            exact mul_le_mul_of_nonneg_left hK_upper_le hp_nonneg
      _ = (1 + ε) * L := by
            rw [hp_formula]
            calc
              (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) *
                  (2 * ((1 + ε) * Real.sqrt ((n : ℝ) * L))) =
                  (1 + ε) *
                    (Real.sqrt (L / (n : ℝ)) * Real.sqrt ((n : ℝ) * L)) := by
                ring
              _ = (1 + ε) * L := by rw [hsqrt_product]
  have hep_pos : 0 < epow := by
    dsimp [epow]
    exact Real.rpow_pos_of_pos hn_pos _
  have hsecond_num :
      16 * (1 + ε) * Real.sqrt L * L ≤ epow := by
    have h := hsecond
    have h' : 4 * (1 + ε) * Real.sqrt L * L ≤ (1 / 4 : ℝ) * epow := by
      rw [← div_le_iff₀ hep_pos]
      simpa [L, epow] using h
    nlinarith
  have hsqrtL_sq : (Real.sqrt L) ^ 2 = L :=
    Real.sq_sqrt (by simpa [L] using hL_nonneg)
  have htail_absorb :
      12 * L ^ 2 ≤ (1 + ε) * Real.sqrt L * epow := by
    have hfactor_nonneg : 0 ≤ (1 + ε) * Real.sqrt L := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsecond_num hfactor_nonneg
    have hleft :
        12 * L ^ 2 ≤ (1 + ε) * Real.sqrt L *
            (16 * (1 + ε) * Real.sqrt L * L) := by
      have hone : 1 ≤ 1 + ε := by linarith
      have hsquare : 1 ≤ (1 + ε) ^ 2 := by nlinarith
      have hL2_nonneg : 0 ≤ L ^ 2 := sq_nonneg L
      have hconst : (12 : ℝ) ≤ 16 * (1 + ε) ^ 2 := by nlinarith
      have hscaled : 12 * L ^ 2 ≤ (16 * (1 + ε) ^ 2) * L ^ 2 :=
        mul_le_mul_of_nonneg_right hconst hL2_nonneg
      have heq :
          (1 + ε) * Real.sqrt L *
              (16 * (1 + ε) * Real.sqrt L * L) =
            (16 * (1 + ε) ^ 2) * L ^ 2 := by
        nlinarith [hsqrtL_sq]
      simpa [heq] using hscaled
    exact le_trans hleft hmul
  have hmean_absorb :
      18 * Real.exp 1 * (1 + ε) * L ^ 3 ≤ Real.rpow (n : ℝ) (2 * ε) := by
    have hleft_nonneg : 0 ≤ 16 * (1 + ε) * Real.sqrt L * L := by positivity
    have hsq :
        (16 * (1 + ε) * Real.sqrt L * L) *
            (16 * (1 + ε) * Real.sqrt L * L) ≤ epow * epow := by
      exact mul_le_mul hsecond_num hsecond_num hleft_nonneg (le_of_lt hep_pos)
    have hsq_pow :
        (16 * (1 + ε) * Real.sqrt L * L) ^ 2 ≤ epow ^ 2 := by
      simpa [pow_two] using hsq
    have hsq_expand :
        (16 * (1 + ε) * Real.sqrt L * L) ^ 2 =
          256 * (1 + ε) ^ 2 * L ^ 3 := by
      nlinarith [hsqrtL_sq]
    have hepow_sq :
        epow ^ 2 = Real.rpow (n : ℝ) (2 * ε) := by
      dsimp [epow]
      calc
        (Real.rpow (n : ℝ) ε) ^ 2 =
            Real.rpow (n : ℝ) ε * Real.rpow (n : ℝ) ε := by ring
        _ = Real.rpow (n : ℝ) (ε + ε) := by
          exact (Real.rpow_add hn_pos ε ε).symm
        _ = Real.rpow (n : ℝ) (2 * ε) := by
          congr 1
          ring
    have hconst :
        18 * Real.exp 1 * (1 + ε) ≤ 256 * (1 + ε) ^ 2 := by
      have hexp_le_three : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have hone : 1 ≤ 1 + ε := by linarith
      nlinarith
    have hL3_nonneg : 0 ≤ L ^ 3 := by positivity
    have hconst_scaled :
        18 * Real.exp 1 * (1 + ε) * L ^ 3 ≤
          256 * (1 + ε) ^ 2 * L ^ 3 :=
      mul_le_mul_of_nonneg_right hconst hL3_nonneg
    calc
      18 * Real.exp 1 * (1 + ε) * L ^ 3
          ≤ 256 * (1 + ε) ^ 2 * L ^ 3 := hconst_scaled
      _ = (16 * (1 + ε) * Real.sqrt L * L) ^ 2 := hsq_expand.symm
      _ ≤ epow ^ 2 := hsq_pow
      _ = Real.rpow (n : ℝ) (2 * ε) := hepow_sq
  have hK_lower :
      (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (K : ℝ) := by
    simpa [K] using hk_lower
  have hcompressed_local := hcompressed
  dsimp at hcompressed_local
  have hmean_absorb_compressed :
      36 * Real.exp 1 * (1 + ε) * L ^ 3 ≤
        Real.rpow (n : ℝ) (2 * ε) := by
    simpa [L] using hcompressed_local.1
  have htail_absorb_compressed :
      24 * L ^ 2 ≤ (1 + ε) * Real.sqrt L * epow := by
    simpa [L, epow] using hcompressed_local.2
  exact MediumClosedPairsNaturalTailHypotheses (α := α) ε n BR BB
    hn_pos hL_pos hε_pos hε_lt_one hsize hK_lower
    (by simpa [K, p, L] using hpK)
    hmean_absorb_compressed htail_absorb_compressed
