import Tablet.ParameterHierarchyEventualComparisons
import Tablet.RealChooseTwo
import Tablet.TwoBiteHugeCutoff
import Tablet.TwoBiteNaturalIndependenceScale

-- [TABLET NODE: HugeFamilyEventualNumerics]

theorem HugeFamilyEventualNumerics :
    ∀ {n k : ℕ} {ε ε1 ε2 : ℝ} {n0 : ℕ},
      ParameterHierarchyEventualComparisons ε ε1 ε2 n0 →
      n0 < n →
      k = TwoBiteNaturalIndependenceScale (1 + ε) n →
      let t1 : ℝ := TwoBiteHugeCutoff n
      let C : ℝ := 100 * (Real.log (n : ℝ)) ^ 3
      0 < t1 ∧ 0 ≤ C ∧
        RealChooseTwo (2 * (k : ℝ) / t1 + 1) * C ≤ (1 / 2 : ℝ) * (k : ℝ) := by
-- BODY
  intro n k ε ε1 ε2 n0 hcomparisons hn hk
  dsimp
  let L : ℝ := Real.log (n : ℝ)
  let t0 : ℝ := Real.sqrt ((n : ℝ) * L) / Real.log L
  have hcomp := hcomparisons n hn
  dsimp [ParameterHierarchyEventualComparisons, TwoBiteHugeCutoff, L] at hcomp
  rcases hcomp with
    ⟨hm_pos, _hp_nonneg, _hp_le, hpm_ge_one, _hkReal_le, _hk_lt,
      _hm_le, _hmReal_lt, _h9, _h10, _h11, _h12, _h13, _h14, _h15,
      hchoose, _h17, _h18, _h19, _h20, _h21, heps2_nonneg, _heps2_le,
      hpm_le_t1, _hrest⟩
  have ht0_pos : 0 < t0 := by
    by_contra ht_not
    have ht_nonpos : t0 ≤ 0 := le_of_not_gt ht_not
    have hcoef_nonneg : 0 ≤ ε2 / 100 := by positivity
    have hprod_nonpos : (ε2 / 100) * t0 ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ht_nonpos
    have : 1 ≤ (ε2 / 100) * t0 := le_trans hpm_ge_one hpm_le_t1
    linarith only [this, hprod_nonpos]
  have hp_pos : 0 < (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) := by
    by_contra hp_not
    have hp_nonpos : (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ)) ≤ 0 :=
      le_of_not_gt hp_not
    have hm_nonneg : 0 ≤ (TwoBiteNaturalReducedVertexCount n : ℝ) := le_of_lt hm_pos
    have hprod_nonpos :
        2 * ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) *
            (TwoBiteNaturalReducedVertexCount n : ℝ) ≤ 0 := by
      have hleft_nonpos :
          2 * ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by norm_num) hp_nonpos
      exact mul_nonpos_of_nonpos_of_nonneg hleft_nonpos hm_nonneg
    linarith only [hpm_ge_one, hprod_nonpos]
  have hsqrt_pos : 0 < Real.sqrt (L / (n : ℝ)) := by
    have hmul : 0 < (2 : ℝ) * ((1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))) :=
      mul_pos (by norm_num) hp_pos
    simpa [mul_assoc] using hmul
  have harg_pos : 0 < L / (n : ℝ) := Real.sqrt_pos.mp hsqrt_pos
  have hn_pos_nat : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le n0) hn
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hL_pos : 0 < L := by
    have hmul_pos : 0 < (L / (n : ℝ)) * (n : ℝ) := mul_pos harg_pos hn_pos
    rwa [div_mul_cancel₀ L (ne_of_gt hn_pos)] at hmul_pos
  have hC_nonneg : 0 ≤ 100 * L ^ 3 := by
    nlinarith [sq_nonneg L, hL_pos]
  have ht_eq : t0 = TwoBiteHugeCutoff n := by
    simp [t0, L, TwoBiteHugeCutoff]
  have ht_pos : 0 < TwoBiteHugeCutoff n := by
    simpa [← ht_eq] using ht0_pos
  have hk_cast :
      ((TwoBiteNaturalIndependenceScale (1 + ε) n : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast hk.symm
  refine ⟨ht_pos, by simpa [L] using hC_nonneg, ?_⟩
  change
    RealChooseTwo (2 * (k : ℝ) / TwoBiteHugeCutoff n + 1) *
        (100 * Real.log (n : ℝ) ^ 3) ≤
      (1 / 2 : ℝ) * (k : ℝ)
  rw [TwoBiteHugeCutoff]
  simpa [L, hk_cast] using hchoose
