import Tablet.RealChooseTwo

-- [TABLET NODE: ParameterHierarchyT24Algebra]

theorem ParameterHierarchyT24Algebra :
    ∀ η k : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η)
      0 < (n : ℝ) →
      0 ≤ L →
      k < 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) →
      RealChooseTwo (Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
        Real.rpow (n : ℝ) (1 / 4 : ℝ) ^ 2 →
      100 * L ^ 3 / Real.rpow (n : ℝ) η ≤ (1 / 2 : ℝ) →
      2 * (1 + η) * Real.sqrt L / Real.rpow (n : ℝ) η < (1 / 2 : ℝ) →
      k < Real.rpow (n : ℝ) (1 / 4 : ℝ) * t2 -
        RealChooseTwo (Real.rpow (n : ℝ) (1 / 4 : ℝ)) * (100 * L ^ 3) := by
-- BODY
  intro η k n
  dsimp
  let L := Real.log (n : ℝ)
  let q := Real.rpow (n : ℝ) (1 / 4 : ℝ)
  let t2 := Real.rpow (n : ℝ) ((1 / 4 : ℝ) + η)
  let e := Real.rpow (n : ℝ) η
  intro hn_pos hL_nonneg hk_upper hchoose_upper hloss_threshold hsqrt_threshold
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos hn_pos _
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.rpow_pos_of_pos hn_pos _
  have he_nonneg : 0 ≤ e := le_of_lt he_pos
  have ht2_pos : 0 < t2 := by
    dsimp [t2]
    exact Real.rpow_pos_of_pos hn_pos _
  have hA_pos : 0 < q * t2 := mul_pos hq_pos ht2_pos
  have hL_cube_nonneg : 0 ≤ L ^ 3 := by positivity
  have hfactor_nonneg : 0 ≤ 100 * L ^ 3 := by positivity
  have ht2_eq : t2 = q * e := by
    dsimp [t2, q, e]
    exact Real.rpow_add hn_pos (1 / 4 : ℝ) η
  have hA_eq : q * t2 = Real.sqrt (n : ℝ) * e := by
    calc
      q * t2 = q * (q * e) := by rw [ht2_eq]
      _ = q ^ 2 * e := by ring
      _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) * e := by
        have hq_sq : q ^ 2 = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
          dsimp [q]
          calc
            (Real.rpow (n : ℝ) (1 / 4 : ℝ)) ^ 2 =
                Real.rpow (n : ℝ) (1 / 4 : ℝ) *
                  Real.rpow (n : ℝ) (1 / 4 : ℝ) := by ring
            _ = Real.rpow (n : ℝ) ((1 / 4 : ℝ) + (1 / 4 : ℝ)) := by
              exact (Real.rpow_add hn_pos (1 / 4 : ℝ) (1 / 4 : ℝ)).symm
            _ = Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
              congr 1
              ring
        rw [hq_sq]
      _ = Real.sqrt (n : ℝ) * e :=
        congrArg (fun x : ℝ => x * e) (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hk_half :
      k < (1 / 2 : ℝ) * (q * t2) := by
    have hrewrite :
        2 * (1 + η) * Real.sqrt ((n : ℝ) * L) =
          (2 * (1 + η) * Real.sqrt L / e) * (q * t2) := by
      rw [hA_eq]
      rw [Real.sqrt_mul hn_nonneg]
      field_simp [ne_of_gt he_pos]
    have hscale_lt :
        (2 * (1 + η) * Real.sqrt L / e) * (q * t2) <
          (1 / 2 : ℝ) * (q * t2) :=
      mul_lt_mul_of_pos_right hsqrt_threshold hA_pos
    calc
      k < 2 * (1 + η) * Real.sqrt ((n : ℝ) * L) := hk_upper
      _ = (2 * (1 + η) * Real.sqrt L / e) * (q * t2) := hrewrite
      _ < (1 / 2 : ℝ) * (q * t2) := hscale_lt
  have hloss_num :
      100 * L ^ 3 ≤ (1 / 2 : ℝ) * e := by
    have hloss_threshold_L : 100 * L ^ 3 / e ≤ (1 / 2 : ℝ) := by
      simpa [L, e] using hloss_threshold
    rw [div_le_iff₀ he_pos] at hloss_threshold_L
    simpa [one_mul] using hloss_threshold_L
  have hloss_half :
      RealChooseTwo q * (100 * L ^ 3) ≤ (1 / 2 : ℝ) * (q * t2) := by
    calc
      RealChooseTwo q * (100 * L ^ 3) ≤ q ^ 2 * (100 * L ^ 3) :=
        mul_le_mul_of_nonneg_right hchoose_upper hfactor_nonneg
      _ ≤ q ^ 2 * ((1 / 2 : ℝ) * e) :=
        mul_le_mul_of_nonneg_left hloss_num (sq_nonneg q)
      _ = (1 / 2 : ℝ) * (q * t2) := by
        rw [ht2_eq]
        ring
  have hsum_lt :
      k + RealChooseTwo q * (100 * L ^ 3) < q * t2 := by
    calc
      k + RealChooseTwo q * (100 * L ^ 3) <
          (1 / 2 : ℝ) * (q * t2) + (1 / 2 : ℝ) * (q * t2) :=
        add_lt_add_of_lt_of_le hk_half hloss_half
      _ = q * t2 := by ring
  rw [lt_sub_iff_add_lt]
  simpa [L, q, t2] using hsum_lt
