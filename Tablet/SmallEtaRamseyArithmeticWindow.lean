import Tablet.RamseyScale

-- [TABLET NODE: SmallEtaRamseyArithmeticWindow]

theorem SmallEtaRamseyArithmeticWindow :
    ∀ η : ℝ, 0 < η → η < (1 / 2 : ℝ) →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ n0 : ℕ, ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
          ∃ N : ℕ,
            n0 ≤ N ∧
              ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) ∧
                (1 + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) < (k : ℝ) := by
-- BODY
  intro η hη hηsmall
  let c : ℝ := (1 / 2 : ℝ) - η / 2
  let δ : ℝ := η / 2
  let ε : ℝ := η / 8
  have hcpos : 0 < c := by
    dsimp [c]
    linarith
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have h1εpos : 0 < 1 + ε := by positivity
  have h2ceps : 2 * c * (1 + ε) ^ 2 < 1 := by
    dsimp [c, ε]
    calc
      2 * ((1 : ℝ) / 2 - η / 2) * (1 + η / 8) ^ 2
          = (1 - η) * (1 + η / 8) ^ 2 := by ring
      _ < 1 := by
        have hs : 0 ≤ η ^ 2 := sq_nonneg η
        nlinarith [hη, hs]
  refine ⟨ε, hεpos, ?_⟩
  intro n0
  let Bn : ℝ := ((n0 : ℝ) + 1) / c + 1
  let B4 : ℝ := (4 : ℝ) / c + 1
  let Bδ : ℝ := (1 : ℝ) / δ + 1
  let Be : ℝ := Real.exp c + 1
  let M : ℝ := max (3 : ℝ) (max Be (max Bn (max B4 Bδ)))
  obtain ⟨k0, hk0M⟩ := exists_nat_gt M
  refine ⟨k0, ?_⟩
  intro k hk
  have hk0le : (k0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hMlt : M < (k : ℝ) := lt_of_lt_of_le hk0M hk0le
  have h3leM : (3 : ℝ) ≤ M := by dsimp [M]; simp
  have h3lt : (3 : ℝ) < (k : ℝ) := lt_of_le_of_lt h3leM hMlt
  have hkpos : 0 < (k : ℝ) := by linarith
  have hk_nonneg : 0 ≤ (k : ℝ) := hkpos.le
  have hk_gt_one : (1 : ℝ) < (k : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_gt_one
  have hlog_ne : Real.log (k : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hlog_le_k : Real.log (k : ℝ) ≤ (k : ℝ) :=
    Real.log_le_self hk_nonneg
  have hBe_leM : Be ≤ M := by dsimp [M, Be, Bn, B4, Bδ]; simp
  have hexp_lt_k : Real.exp c < (k : ℝ) := by
    linarith [hBe_leM, hMlt]
  have hlog_gt_c : c < Real.log (k : ℝ) :=
    (Real.lt_log_iff_exp_lt hkpos).mpr hexp_lt_k
  let R : ℝ := (k : ℝ) ^ 2 / Real.log (k : ℝ)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact div_nonneg (sq_nonneg _) hlog_pos.le
  have hk_le_R : (k : ℝ) ≤ R := by
    dsimp [R]
    rw [le_div_iff₀ hlog_pos]
    have hmul := mul_le_mul_of_nonneg_left hlog_le_k hk_nonneg
    nlinarith
  have hBn_leM : Bn ≤ M := by dsimp [M, Bn, B4, Bδ, Be]; simp
  have hBn_lt_k : Bn < (k : ℝ) := lt_of_le_of_lt hBn_leM hMlt
  have hn0_div_lt : ((n0 : ℝ) + 1) / c < (k : ℝ) := by
    dsimp [Bn] at hBn_lt_k
    linarith
  have hn0_lt_ck : ((n0 : ℝ) + 1) < c * (k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hcpos).mp hn0_div_lt
  have hn0_bound : ((n0 : ℝ) + 1) ≤ c * R := by
    have hck_le : c * (k : ℝ) ≤ c * R :=
      mul_le_mul_of_nonneg_left hk_le_R hcpos.le
    exact le_trans hn0_lt_ck.le hck_le
  have hB4_leM : B4 ≤ M := by dsimp [M, Bn, B4, Bδ, Be]; simp
  have hB4_lt_k : B4 < (k : ℝ) := lt_of_le_of_lt hB4_leM hMlt
  have h4_div_lt : (4 : ℝ) / c < (k : ℝ) := by
    dsimp [B4] at hB4_lt_k
    linarith
  have h4_lt_ck : (4 : ℝ) < c * (k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hcpos).mp h4_div_lt
  have h4_bound : (4 : ℝ) ≤ c * R := by
    have hck_le : c * (k : ℝ) ≤ c * R :=
      mul_le_mul_of_nonneg_left hk_le_R hcpos.le
    exact le_trans h4_lt_ck.le hck_le
  have hBδ_leM : Bδ ≤ M := by dsimp [M, Bn, B4, Bδ, Be]; simp
  have hBδ_lt_k : Bδ < (k : ℝ) := lt_of_le_of_lt hBδ_leM hMlt
  have hδ_div_lt : (1 : ℝ) / δ < (k : ℝ) := by
    dsimp [Bδ] at hBδ_lt_k
    linarith
  have h1_lt_δk : (1 : ℝ) < δ * (k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hδpos).mp hδ_div_lt
  have hδ_bound : (1 : ℝ) ≤ δ * R := by
    have hδk_le : δ * (k : ℝ) ≤ δ * R :=
      mul_le_mul_of_nonneg_left hk_le_R hδpos.le
    exact le_trans h1_lt_δk.le hδk_le
  let X : ℝ := c * R
  let N : ℕ := Nat.floor X
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg hcpos.le hR_nonneg
  have hN_le_X : (N : ℝ) ≤ X := Nat.floor_le hX_nonneg
  have hX_sub_le_N : X - 1 ≤ (N : ℝ) :=
    (Nat.sub_one_lt_floor X).le
  have hN_large_real : (n0 : ℝ) ≤ (N : ℝ) := by
    have hX_ge : ((n0 : ℝ) + 1) ≤ X := by
      simpa [X] using hn0_bound
    have : (n0 : ℝ) ≤ X - 1 := by linarith
    exact le_trans this hX_sub_le_N
  have hN_large : n0 ≤ N := by
    exact_mod_cast hN_large_real
  have hN_ge3_real : (3 : ℝ) ≤ (N : ℝ) := by
    have hX_ge4 : (4 : ℝ) ≤ X := by
      simpa [X] using h4_bound
    linarith
  have hscale_real : ((1 : ℝ) / 2 - η) * R ≤ (N : ℝ) := by
    have hcoeff : c - δ = ((1 : ℝ) / 2 - η) := by
      dsimp [c, δ]
      ring
    have hlow : ((1 : ℝ) / 2 - η) * R ≤ X - 1 := by
      calc
        ((1 : ℝ) / 2 - η) * R = (c - δ) * R := by rw [← hcoeff]
        _ = c * R - δ * R := by ring
        _ ≤ c * R - 1 := by linarith [hδ_bound]
        _ = X - 1 := by rfl
    exact le_trans hlow hX_sub_le_N
  have hscale :
      ((1 : ℝ) / 2 - η) * RamseyScale k ≤ (N : ℝ) := by
    unfold RamseyScale
    simpa [R] using hscale_real
  have hk2pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hkpos
  have hX_log_lt :
      X * Real.log (k : ℝ) < ((k : ℝ) ^ 2) * Real.log (k : ℝ) := by
    dsimp [X, R]
    calc
      c * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) * Real.log (k : ℝ)
          = c * (k : ℝ) ^ 2 := by
            field_simp [hlog_ne]
      _ < Real.log (k : ℝ) * (k : ℝ) ^ 2 := by
            exact mul_lt_mul_of_pos_right hlog_gt_c hk2pos
      _ = ((k : ℝ) ^ 2) * Real.log (k : ℝ) := by ring
  have hX_lt_k2 : X < (k : ℝ) ^ 2 := by
    nlinarith [hX_log_lt, hlog_pos]
  have hN_le_k2 : (N : ℝ) ≤ (k : ℝ) ^ 2 :=
    le_trans hN_le_X hX_lt_k2.le
  have hNpos : 0 < (N : ℝ) := by linarith
  have hN_gt_one : (1 : ℝ) < (N : ℝ) := by linarith
  have hlogN_pos : 0 < Real.log (N : ℝ) := Real.log_pos hN_gt_one
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := hlogN_pos.le
  have hlogN_le_logk2 :
      Real.log (N : ℝ) ≤ Real.log ((k : ℝ) ^ 2) :=
    Real.log_le_log hNpos hN_le_k2
  have hlogN_le_2logk :
      Real.log (N : ℝ) ≤ 2 * Real.log (k : ℝ) := by
    simpa [Real.log_pow] using hlogN_le_logk2
  have hNlog_le :
      (N : ℝ) * Real.log (N : ℝ) ≤ X * (2 * Real.log (k : ℝ)) := by
    exact mul_le_mul hN_le_X hlogN_le_2logk hlogN_nonneg hX_nonneg
  have hX_twolog :
      X * (2 * Real.log (k : ℝ)) = 2 * c * (k : ℝ) ^ 2 := by
    dsimp [X, R]
    field_simp [hlog_ne]
  have hNlog_le_2c :
      (N : ℝ) * Real.log (N : ℝ) ≤ 2 * c * (k : ℝ) ^ 2 := by
    simpa [hX_twolog] using hNlog_le
  have hleft_le :
      (1 + ε) ^ 2 * ((N : ℝ) * Real.log (N : ℝ)) ≤
        (1 + ε) ^ 2 * (2 * c * (k : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hNlog_le_2c (sq_nonneg (1 + ε))
  have hright_lt :
      (1 + ε) ^ 2 * (2 * c * (k : ℝ) ^ 2) < (k : ℝ) ^ 2 := by
    have hm := mul_lt_mul_of_pos_right h2ceps hk2pos
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm
  have hsq_lt :
      (1 + ε) ^ 2 * ((N : ℝ) * Real.log (N : ℝ)) < (k : ℝ) ^ 2 :=
    lt_of_le_of_lt hleft_le hright_lt
  have hsqrt_lt :
      Real.sqrt ((1 + ε) ^ 2 * ((N : ℝ) * Real.log (N : ℝ))) < (k : ℝ) := by
    rw [Real.sqrt_lt' hkpos]
    exact hsq_lt
  have hsqrt_eq :
      Real.sqrt ((1 + ε) ^ 2 * ((N : ℝ) * Real.log (N : ℝ))) =
        (1 + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
    rw [Real.sqrt_mul (sq_nonneg (1 + ε))]
    rw [Real.sqrt_sq h1εpos.le]
  have hthreshold :
      (1 + ε) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) < (k : ℝ) := by
    rwa [hsqrt_eq] at hsqrt_lt
  exact ⟨N, hN_large, hscale, hthreshold⟩
