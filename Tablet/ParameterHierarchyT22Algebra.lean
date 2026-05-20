import Tablet.TwoBiteHugeCutoff
import Tablet.TwoBiteNaturalReducedVertexCount

-- [TABLET NODE: ParameterHierarchyT22Algebra]

theorem ParameterHierarchyT22Algebra :
    ∀ η ε2 : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
      let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
      let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η)
      0 ≤ ε2 →
      ε2 ≤ 1 →
      0 < (n : ℝ) →
      0 < L →
      0 < Real.log L →
      0 ≤ p →
      0 ≤ m →
      2 * p * m ≤ Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ) →
      2 * Real.log L * Real.sqrt L /
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) < (1 / 2 : ℝ) →
      Real.log L / L < (1 / 2 : ℝ) →
      (1 + ε2) * L ^ 2 * (t2 / L) +
          L * (1 + ε2) * p * m <
        TwoBiteHugeCutoff n := by
-- BODY
  intro η ε2 n
  dsimp
  let L := Real.log (n : ℝ)
  let m := (TwoBiteNaturalReducedVertexCount n : ℝ)
  let p := (1 / 2 : ℝ) * Real.sqrt (L / (n : ℝ))
  let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η)
  intro hε2_nonneg hε2_le_one hn_pos hL_pos hlogL_pos hp_nonneg hm_nonneg
    hmass hfirst_threshold hsecond_threshold
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hsqrtL_nonneg : 0 ≤ Real.sqrt L := le_of_lt hsqrtL_pos
  have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
  have ht2_pos : 0 < t2 := by
    dsimp [t2]
    exact Real.rpow_pos_of_pos hn_pos _
  have ht2_nonneg : 0 ≤ t2 := le_of_lt ht2_pos
  have hsmall_power_pos :
      0 < Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) :=
    Real.rpow_pos_of_pos hn_pos _
  have hcoeff_nonneg : 0 ≤ 1 + ε2 := by linarith
  have hcoeff_le_two : 1 + ε2 ≤ 2 := by linarith
  have hfirst_le :
      (1 + ε2) * L ^ 2 * (t2 / L) ≤ 2 * L * t2 := by
    have hL_sq_nonneg : 0 ≤ L ^ 2 := sq_nonneg L
    have ht2_div_nonneg : 0 ≤ t2 / L := div_nonneg ht2_nonneg hL_nonneg
    have hmul1 :
        (1 + ε2) * L ^ 2 ≤ 2 * L ^ 2 :=
      mul_le_mul_of_nonneg_right hcoeff_le_two hL_sq_nonneg
    have hmul2 :
        (1 + ε2) * L ^ 2 * (t2 / L) ≤ 2 * L ^ 2 * (t2 / L) :=
      mul_le_mul_of_nonneg_right hmul1 ht2_div_nonneg
    calc
      (1 + ε2) * L ^ 2 * (t2 / L) ≤ 2 * L ^ 2 * (t2 / L) := hmul2
      _ = 2 * L * t2 := by
        field_simp [ne_of_gt hL_pos]
  have hL_rpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    calc
      L ^ (3 / 2 : ℝ) = L ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_add hL_pos]
      _ = L * Real.sqrt L := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hsecond_le :
      L * (1 + ε2) * p * m ≤ Real.sqrt (n : ℝ) / Real.sqrt L := by
    have htwopm_nonneg : 0 ≤ 2 * p * m := by positivity
    have hfactor_nonneg : 0 ≤ L * (2 * p * m) :=
      mul_nonneg hL_nonneg htwopm_nonneg
    have hcoeff_half_le_one : (1 + ε2) / 2 ≤ 1 := by linarith
    calc
      L * (1 + ε2) * p * m =
          ((1 + ε2) / 2) * (L * (2 * p * m)) := by ring
      _ ≤ 1 * (L * (2 * p * m)) :=
        mul_le_mul_of_nonneg_right hcoeff_half_le_one hfactor_nonneg
      _ = L * (2 * p * m) := by ring
      _ ≤ L * (Real.sqrt (n : ℝ) / L ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmass hL_nonneg
      _ = Real.sqrt (n : ℝ) / Real.sqrt L := by
        rw [hL_rpow]
        field_simp [ne_of_gt hL_pos, ne_of_gt hsqrtL_pos]
        exact mul_inv_cancel₀ (ne_of_gt hL_pos)
  have hhuge_eq :
      TwoBiteHugeCutoff n = Real.sqrt (n : ℝ) * Real.sqrt L / Real.log L := by
    dsimp [TwoBiteHugeCutoff, L]
    rw [Real.sqrt_mul hn_nonneg]
  have ht2_mul_small_power :
      t2 * Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) = Real.sqrt (n : ℝ) := by
    dsimp [t2]
    calc
      Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η) *
          Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) =
          Real.rpow (n : ℝ)
            (((1 / 4 : ℝ) + η) + ((1 / 4 : ℝ) - η)) := by
        simpa using
          (Real.rpow_add hn_pos ((1 / 4 : ℝ) + η)
            ((1 / 4 : ℝ) - η)).symm
      _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
        congr 1
        ring
      _ = Real.sqrt (n : ℝ) := by
        exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hfirst_half :
      2 * L * t2 < (1 / 2 : ℝ) * TwoBiteHugeCutoff n := by
    let M : ℝ :=
      Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η) *
        (t2 * L / (Real.log L * Real.sqrt L))
    have hM_pos : 0 < M := by
      dsimp [M]
      positivity
    have hmul := mul_lt_mul_of_pos_right hfirst_threshold hM_pos
    calc
      2 * L * t2 =
          (2 * Real.log L * Real.sqrt L /
              Real.rpow (n : ℝ) ((1 / 4 : ℝ) - η)) * M := by
        dsimp [M]
        field_simp [ne_of_gt hsmall_power_pos, ne_of_gt hlogL_pos,
          ne_of_gt hsqrtL_pos]
        symm
        calc
          L * Real.log L / Real.log L = L * (Real.log L / Real.log L) := by ring
          _ = L * 1 := by rw [div_self (ne_of_gt hlogL_pos)]
          _ = L := by ring
      _ < (1 / 2 : ℝ) * M := hmul
      _ = (1 / 2 : ℝ) * TwoBiteHugeCutoff n := by
        dsimp [M]
        rw [hhuge_eq]
        rw [← ht2_mul_small_power]
        field_simp [ne_of_gt hlogL_pos, ne_of_gt hsqrtL_pos]
        rw [Real.sq_sqrt hL_nonneg]
        change (n : ℝ) ^ (((1 : ℝ) - 4 * η) / 4) * L / Real.log L =
          L * (n : ℝ) ^ (((1 : ℝ) - 4 * η) / 4) / Real.log L
        ring
  have hsecond_half :
      Real.sqrt (n : ℝ) / Real.sqrt L <
        (1 / 2 : ℝ) * TwoBiteHugeCutoff n := by
    have hlogL_lt_half_L : Real.log L < (1 / 2 : ℝ) * L := by
      rw [div_lt_iff₀ hL_pos] at hsecond_threshold
      simpa [one_mul] using hsecond_threshold
    have hden_pos : 0 < Real.sqrt L * Real.log L :=
      mul_pos hsqrtL_pos hlogL_pos
    have hnum_lt :
        Real.sqrt (n : ℝ) * Real.log L <
          Real.sqrt (n : ℝ) * ((1 / 2 : ℝ) * L) :=
      mul_lt_mul_of_pos_left hlogL_lt_half_L hsqrtn_pos
    calc
      Real.sqrt (n : ℝ) / Real.sqrt L =
          (Real.sqrt (n : ℝ) * Real.log L) / (Real.sqrt L * Real.log L) := by
        field_simp [ne_of_gt hsqrtL_pos, ne_of_gt hlogL_pos]
        exact (div_self (ne_of_gt hlogL_pos)).symm
      _ < (Real.sqrt (n : ℝ) * ((1 / 2 : ℝ) * L)) /
          (Real.sqrt L * Real.log L) :=
        div_lt_div_of_pos_right hnum_lt hden_pos
      _ = (1 / 2 : ℝ) * (Real.sqrt (n : ℝ) * Real.sqrt L / Real.log L) := by
        field_simp [ne_of_gt hsqrtL_pos, ne_of_gt hlogL_pos]
        rw [Real.sq_sqrt hL_nonneg]
      _ = (1 / 2 : ℝ) * TwoBiteHugeCutoff n := by
        rw [hhuge_eq]
  have hparts_lt :
      2 * L * t2 + Real.sqrt (n : ℝ) / Real.sqrt L <
        TwoBiteHugeCutoff n := by
    calc
      2 * L * t2 + Real.sqrt (n : ℝ) / Real.sqrt L <
          (1 / 2 : ℝ) * TwoBiteHugeCutoff n +
            (1 / 2 : ℝ) * TwoBiteHugeCutoff n :=
        add_lt_add hfirst_half hsecond_half
      _ = TwoBiteHugeCutoff n := by ring
  exact lt_of_le_of_lt (add_le_add hfirst_le hsecond_le) hparts_lt
