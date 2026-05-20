import Tablet.Preamble

-- [TABLET NODE: ParameterHierarchyT26Algebra]

theorem ParameterHierarchyT26Algebra :
    ∀ η ε1 k : ℝ, ∀ n : ℕ,
      let L := Real.log (n : ℝ)
      let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
      0 < η →
      0 < ε1 →
      0 < (n : ℝ) →
      0 < L →
      0 ≤ k →
      kReal ≤ k →
      2 / L ≤ ε1 / 2 →
      1 / ((1 + η) * Real.rpow (n : ℝ) (1 / 4 : ℝ) * Real.sqrt L) ≤
        ε1 / 2 →
      k * (2 * k / L + Real.rpow (n : ℝ) (1 / 4 : ℝ)) ≤
        ε1 * k ^ 2 := by
-- BODY
  intro η ε1 k n
  dsimp
  let L := Real.log (n : ℝ)
  let q := Real.rpow (n : ℝ) (1 / 4 : ℝ)
  let kReal := (1 + η) * Real.sqrt ((n : ℝ) * L)
  intro hη_pos hε1_pos hn_pos hL_pos hk_nonneg hkReal_le_k hfirst hsecond
  have h_one_add_pos : 0 < 1 + η := by linarith
  have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos hn_pos _
  have hq_nonneg : 0 ≤ q := le_of_lt hq_pos
  have hsqrtL_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hden_pos :
      0 < (1 + η) * q * Real.sqrt L :=
    mul_pos (mul_pos h_one_add_pos hq_pos) hsqrtL_pos
  have hhalf_nonneg : 0 ≤ ε1 / 2 := by positivity
  have hk_sq_nonneg : 0 ≤ k ^ 2 := sq_nonneg k
  have hfirst_bound :
      k * (2 * k / L) ≤ (ε1 / 2) * k ^ 2 := by
    calc
      k * (2 * k / L) = (2 / L) * k ^ 2 := by ring
      _ ≤ (ε1 / 2) * k ^ 2 :=
        mul_le_mul_of_nonneg_right hfirst hk_sq_nonneg
  have hthreshold_mul :
      (1 : ℝ) ≤ (ε1 / 2) * ((1 + η) * q * Real.sqrt L) := by
    have hsecond_q :
        1 / ((1 + η) * q * Real.sqrt L) ≤ ε1 / 2 := by
      simpa [L, q] using hsecond
    rw [div_le_iff₀ hden_pos] at hsecond_q
    simpa [one_mul] using hsecond_q
  have hq_sq_sqrt : q ^ 2 = Real.sqrt (n : ℝ) := by
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
      _ = Real.sqrt (n : ℝ) := by
        exact (Real.sqrt_eq_rpow (n : ℝ)).symm
  have hkReal_eq :
      kReal = (1 + η) * q ^ 2 * Real.sqrt L := by
    dsimp [kReal]
    rw [Real.sqrt_mul (le_of_lt hn_pos)]
    rw [← hq_sq_sqrt]
    ring
  have hq_le_half_kReal :
      q ≤ (ε1 / 2) * kReal := by
    have hmul := mul_le_mul_of_nonneg_right hthreshold_mul hq_nonneg
    calc
      q = 1 * q := by ring
      _ ≤ ((ε1 / 2) * ((1 + η) * q * Real.sqrt L)) * q := hmul
      _ = (ε1 / 2) * ((1 + η) * q ^ 2 * Real.sqrt L) := by ring
      _ = (ε1 / 2) * kReal := by
        rw [hkReal_eq]
  have hq_le_half_k :
      q ≤ (ε1 / 2) * k :=
    le_trans hq_le_half_kReal
      (mul_le_mul_of_nonneg_left hkReal_le_k hhalf_nonneg)
  have hsecond_bound :
      k * q ≤ (ε1 / 2) * k ^ 2 := by
    calc
      k * q ≤ k * ((ε1 / 2) * k) :=
        mul_le_mul_of_nonneg_left hq_le_half_k hk_nonneg
      _ = (ε1 / 2) * k ^ 2 := by ring
  have hmain :
      k * (2 * k / L + q) ≤ ε1 * k ^ 2 := by
    calc
      k * (2 * k / L + q) = k * (2 * k / L) + k * q := by ring
      _ ≤ (ε1 / 2) * k ^ 2 + (ε1 / 2) * k ^ 2 :=
        add_le_add hfirst_bound hsecond_bound
      _ = ε1 * k ^ 2 := by ring
  simpa [q] using hmain
