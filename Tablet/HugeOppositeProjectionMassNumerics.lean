import Tablet.RealChooseTwo
import Tablet.HugeOppositeProjectionExceptionalTailNumerics
import Tablet.HugeOppositeProjectionLargeExceptionalNumerics
import Tablet.HugeOppositeProjectionTwoBlockStretch

-- [TABLET NODE: HugeOppositeProjectionMassNumerics]

set_option maxHeartbeats 1000000 in
theorem HugeOppositeProjectionMassNumerics :
    ∀ {ε1 ε2 D b T : ℝ},
      0 ≤ ε1 →
      0 ≤ ε2 →
      ε2 ≤ 1 →
      3 * ε2 ≤ ε1 / 10 →
      98 ≤ D →
      0 ≤ b →
      0 ≤ T →
      (∃ d : ℕ, D = d) →
      (∃ t : ℕ, T = t) →
      T ≤ (1 + ε2) * D →
        RealChooseTwo T ≤ (1 + ε1) * RealChooseTwo D ∧
          (T ≤ (1 + ε2) * b →
            RealChooseTwo T ≤
              (1 + ε1) *
                (RealChooseTwo b + RealChooseTwo (D - b))) ∧
          ((1 + ε2) * b ≤ T →
            RealChooseTwo ((1 + ε2) * b) +
                RealChooseTwo (T - (1 + ε2) * b) ≤
              (1 + ε1) *
                (RealChooseTwo b + RealChooseTwo (D - b))) := by
-- BODY
  intro ε1 ε2 D b T hε1 hε2 hε2_le_one hscale hD hb hT hDnat hTnat hTle
  have h30 : 30 * ε2 ≤ ε1 := by
    nlinarith
  have h10 : 10 * ε2 ≤ ε1 := by
    nlinarith
  have hfactor10 : 1 + 10 * ε2 ≤ 1 + ε1 := by
    linarith only [h10]
  have hD_nonneg : 0 ≤ D := by
    linarith
  have hD_ge_two : 2 ≤ D := by
    linarith
  have hD_minus_one_nonneg : 0 ≤ D - 1 := by
    linarith
  have hD_minus_two_nonneg : 0 ≤ D - 2 := by
    linarith
  have hChooseD_nonneg : 0 ≤ RealChooseTwo D := by
    unfold RealChooseTwo
    have hprod : 0 ≤ D * (D - 1) :=
      mul_nonneg hD_nonneg hD_minus_one_nonneg
    nlinarith
  have hPairMass_nonneg :
      0 ≤ RealChooseTwo b + RealChooseTwo (D - b) := by
    unfold RealChooseTwo
    have hsq : 0 ≤ (b - D / 2) ^ 2 := sq_nonneg (b - D / 2)
    have hDprod : 0 ≤ D * (D - 2) :=
      mul_nonneg hD_nonneg hD_minus_two_nonneg
    nlinarith [hsq, hDprod]
  have hstretchedD :
      RealChooseTwo ((1 + ε2) * D) ≤
        (1 + 10 * ε2) * RealChooseTwo D := by
    unfold RealChooseTwo
    have hDsq_nonneg : 0 ≤ D ^ 2 := sq_nonneg D
    have hcoef_nonneg : 0 ≤ (8 - ε2) * D ^ 2 - 9 * D := by
      nlinarith
    have hgap_nonneg :
        0 ≤ ε2 * ((8 - ε2) * D ^ 2 - 9 * D) :=
      mul_nonneg hε2 hcoef_nonneg
    nlinarith [hgap_nonneg]
  have hstretchedD_eps :
      RealChooseTwo ((1 + ε2) * D) ≤
        (1 + ε1) * RealChooseTwo D := by
    exact le_trans hstretchedD (by nlinarith [h10, hChooseD_nonneg])
  have hChoose_mono_on_one :
      ∀ {u v : ℝ}, 1 ≤ u → u ≤ v →
        RealChooseTwo u ≤ RealChooseTwo v := by
    intro u v hu hv
    unfold RealChooseTwo
    have hdiff :
        0 ≤ (v - u) * (u + v - 1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith [hdiff]
  have hChoose_nonpos_on_unit :
      ∀ {u : ℝ}, 0 ≤ u → u ≤ 1 → RealChooseTwo u ≤ 0 := by
    intro u hu0 hu1
    have hu_minus_nonpos : u - 1 ≤ 0 := by
      linarith only [hu1]
    have hprod_nonpos : u * (u - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (a := u) (b := u - 1)
        hu0 hu_minus_nonpos
    unfold RealChooseTwo
    nlinarith only [hprod_nonpos]
  have hstretchedB_regular :
      D - b ≤ 0 ∨ 1 ≤ D - b →
        RealChooseTwo ((1 + ε2) * b) ≤
          (1 + 10 * ε2) *
            (RealChooseTwo b + RealChooseTwo (D - b)) := by
    intro hregular
    have hfirst_nonneg : 0 ≤ (D - b) * (D - b - 1) := by
      rcases hregular with hleft | hright
      · exact mul_nonneg_of_nonpos_of_nonpos hleft (by linarith)
      · exact mul_nonneg (by linarith) (by linarith)
    have hdisc_part_nonneg : 0 ≤ 280 * D ^ 2 - 640 * D - 1 := by
      nlinarith
    have hquad_square :
        0 ≤ (34 * b - 20 * D + 1) ^ 2 :=
      sq_nonneg (34 * b - 20 * D + 1)
    have hquad_nonneg :
        0 ≤ 17 * b ^ 2 - 20 * D * b + 10 * D ^ 2 - 10 * D + b := by
      nlinarith [hquad_square, hdisc_part_nonneg]
    have hb_sq_nonneg : 0 ≤ b ^ 2 := sq_nonneg b
    have hinside_nonneg :
        0 ≤
          (18 * b ^ 2 - 20 * D * b + 10 * D ^ 2 - 10 * D + b) -
            ε2 * b ^ 2 := by
      have htail : 0 ≤ (1 - ε2) * b ^ 2 :=
        mul_nonneg (by linarith) hb_sq_nonneg
      nlinarith [hquad_nonneg, htail]
    have heps_part_nonneg :
        0 ≤ ε2 *
          ((18 * b ^ 2 - 20 * D * b + 10 * D ^ 2 - 10 * D + b) -
            ε2 * b ^ 2) :=
      mul_nonneg hε2 hinside_nonneg
    unfold RealChooseTwo
    nlinarith [hfirst_nonneg, heps_part_nonneg]
  have hOneBlock :
      RealChooseTwo T ≤ (1 + ε1) * RealChooseTwo D := by
    rcases hTnat with ⟨t, ht⟩
    subst T
    by_cases ht_le_one : t ≤ 1
    · have ht_nonneg_real : 0 ≤ (t : ℝ) := by
        exact_mod_cast Nat.zero_le t
      have ht_real_le_one : (t : ℝ) ≤ 1 := by
        exact_mod_cast ht_le_one
      have hChooseT_nonpos : RealChooseTwo (t : ℝ) ≤ 0 := by
        unfold RealChooseTwo
        nlinarith
      exact le_trans hChooseT_nonpos
        (mul_nonneg (by nlinarith [hε1]) hChooseD_nonneg)
    · have ht_ge_two : 2 ≤ t := by
        omega
      have ht_ge_one_real : (1 : ℝ) ≤ t := by
        exact_mod_cast (by omega : 1 ≤ t)
      let A : ℝ := (1 + ε2) * D
      have hT_le_A : (t : ℝ) ≤ A := by
        simpa [A] using hTle
      have hA_ge_one : 1 ≤ A :=
        le_trans ht_ge_one_real hT_le_A
      have hmono : RealChooseTwo (t : ℝ) ≤ RealChooseTwo A := by
        unfold RealChooseTwo
        have hdiff :
            0 ≤ (A - (t : ℝ)) * ((t : ℝ) + A - 1) := by
          exact mul_nonneg (by linarith) (by linarith)
        nlinarith [hdiff]
      have hA_bound : RealChooseTwo A ≤ (1 + ε1) * RealChooseTwo D := by
        simpa [A] using hstretchedD_eps
      exact le_trans hmono hA_bound
  have hSmall_regular :
      T ≤ (1 + ε2) * b →
        D - b ≤ 0 ∨ 1 ≤ D - b →
          RealChooseTwo T ≤
            (1 + ε1) * (RealChooseTwo b + RealChooseTwo (D - b)) := by
    intro hsmallMass hregular
    let M : ℝ := (1 + ε2) * b
    have hM_regular :
        RealChooseTwo M ≤
          (1 + 10 * ε2) *
            (RealChooseTwo b + RealChooseTwo (D - b)) := by
      simpa [M] using hstretchedB_regular hregular
    have hM_eps :
        RealChooseTwo M ≤
          (1 + ε1) * (RealChooseTwo b + RealChooseTwo (D - b)) := by
      exact le_trans hM_regular (by nlinarith [h10, hPairMass_nonneg])
    by_cases hT_le_one : T ≤ 1
    · have hChooseT_nonpos : RealChooseTwo T ≤ 0 := by
        unfold RealChooseTwo
        nlinarith
      exact le_trans hChooseT_nonpos
        (mul_nonneg (by nlinarith [hε1]) hPairMass_nonneg)
    · have hT_ge_one : 1 ≤ T := by
        linarith
      have hT_le_M : T ≤ M := by
        simpa [M] using hsmallMass
      have hmono : RealChooseTwo T ≤ RealChooseTwo M :=
        hChoose_mono_on_one hT_ge_one hT_le_M
      exact le_trans hmono hM_eps
  refine ⟨hOneBlock, ?_, ?_⟩
  · intro hsmallMass
    by_cases hregular : D - b ≤ 0 ∨ 1 ≤ D - b
    · exact hSmall_regular hsmallMass hregular
    · have hdb_pos : 0 < D - b := by
        by_contra hnot
        have hleft : D - b ≤ 0 := le_of_not_gt hnot
        exact hregular (Or.inl hleft)
      have hdb_lt_one : D - b < 1 := by
        by_contra hnot
        have hright : 1 ≤ D - b := le_of_not_gt hnot
        exact hregular (Or.inr hright)
      by_cases hT_le_one : T ≤ 1
      · have hChooseT_nonpos : RealChooseTwo T ≤ 0 := by
          unfold RealChooseTwo
          nlinarith [hT, hT_le_one]
        exact le_trans hChooseT_nonpos
          (mul_nonneg (by nlinarith [hε1]) hPairMass_nonneg)
      · rcases hDnat with ⟨d, hD_eq⟩
        rcases hTnat with ⟨t, hT_eq⟩
        have hd_ge_98 : 98 ≤ d := by
          have hd_real : (98 : ℝ) ≤ d := by
            nlinarith [hD, hD_eq]
          exact_mod_cast hd_real
        by_cases ht_le_d_minus_one : t ≤ d - 1
        · have hT_ge_one : 1 ≤ T := by
            exact le_of_lt (lt_of_not_ge hT_le_one)
          have ht_add_le_d : t + 1 ≤ d := by
            omega
          have ht_add_le_d_real : (t : ℝ) + 1 ≤ (d : ℝ) := by
            exact_mod_cast ht_add_le_d
          have hT_le_D_minus_one : T ≤ D - 1 := by
            nlinarith [hT_eq, hD_eq, ht_add_le_d_real]
          have hmono :
              RealChooseTwo T ≤ RealChooseTwo (D - 1) :=
            hChoose_mono_on_one hT_ge_one hT_le_D_minus_one
          have hQ_ge_D_minus_one :
              RealChooseTwo (D - 1) ≤
                RealChooseTwo b + RealChooseTwo (D - b) := by
            unfold RealChooseTwo
            have hprod :
                0 ≤ (1 - (D - b)) * (b - 1) :=
              mul_nonneg (by linarith [hdb_lt_one]) (by linarith [hD, hdb_lt_one])
            nlinarith only [hprod]
          have hQ_le_epsQ :
              RealChooseTwo b + RealChooseTwo (D - b) ≤
                (1 + ε1) * (RealChooseTwo b + RealChooseTwo (D - b)) := by
            have hmul_nonneg :
                0 ≤ ε1 * (RealChooseTwo b + RealChooseTwo (D - b)) :=
              mul_nonneg hε1 hPairMass_nonneg
            nlinarith only [hmul_nonneg]
          exact le_trans hmono (le_trans hQ_ge_D_minus_one hQ_le_epsQ)
        · have hd_le_t : d ≤ t := by
            omega
          obtain ⟨r, ht_eq_d_add_r⟩ := Nat.exists_eq_add_of_le hd_le_t
          let u : ℝ := D - b
          have hu_pos : 0 < u := by
            simpa [u] using hdb_pos
          have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
          have hu_lt_one : u < 1 := by
            simpa [u] using hdb_lt_one
          have hDb_eq_u : D - b = u := by
            rfl
          have hb_eq_d_sub_u : b = (d : ℝ) - u := by
            dsimp [u]
            rw [hD_eq]
            ring
          have ht_real_eq : (t : ℝ) = (d : ℝ) + (r : ℝ) := by
            exact_mod_cast ht_eq_d_add_r
          have hT_real_eq : T = (d : ℝ) + (r : ℝ) := by
            rw [hT_eq, ht_real_eq]
          have hd_ge_98_real : (98 : ℝ) ≤ d := by
            exact_mod_cast hd_ge_98
          have hd_nonneg_real : 0 ≤ (d : ℝ) := by
            linarith
          have hsmallMass' :
              (d : ℝ) + (r : ℝ) ≤ (1 + ε2) * ((d : ℝ) - u) := by
            calc
              (d : ℝ) + (r : ℝ) = T := by
                rw [hT_real_eq]
              _ ≤ (1 + ε2) * b := hsmallMass
              _ = (1 + ε2) * ((d : ℝ) - u) := by
                rw [hb_eq_d_sub_u]
          have hru_le_eps_du :
              (r : ℝ) + u ≤ ε2 * ((d : ℝ) - u) := by
            calc
              (r : ℝ) + u =
                  ((d : ℝ) + (r : ℝ)) - ((d : ℝ) - u) := by
                ring
              _ ≤ (1 + ε2) * ((d : ℝ) - u) - ((d : ℝ) - u) :=
                sub_le_sub_right hsmallMass' ((d : ℝ) - u)
              _ = ε2 * ((d : ℝ) - u) := by
                ring
          have hru_le_eps_d :
              (r : ℝ) + u ≤ ε2 * (d : ℝ) := by
            have heps_u_nonneg : 0 ≤ ε2 * u := mul_nonneg hε2 hu_nonneg
            calc
              (r : ℝ) + u ≤ ε2 * ((d : ℝ) - u) := hru_le_eps_du
              _ = ε2 * (d : ℝ) - ε2 * u := by
                ring
              _ ≤ ε2 * (d : ℝ) := by
                linarith
          have hr_nonneg : 0 ≤ (r : ℝ) := by
            exact_mod_cast Nat.zero_le r
          have hr_le_d_real : (r : ℝ) ≤ (d : ℝ) := by
            have hru_ge_r : (r : ℝ) ≤ (r : ℝ) + u := by
              linarith only [hu_nonneg]
            have heps_d_le_d : ε2 * (d : ℝ) ≤ d := by
              calc
                ε2 * (d : ℝ) ≤ 1 * (d : ℝ) :=
                  mul_le_mul_of_nonneg_right hε2_le_one hd_nonneg_real
                _ = d := by
                  ring
            exact le_trans hru_ge_r (le_trans hru_le_eps_d heps_d_le_d)
          exact (by
            have htail :=
              HugeOppositeProjectionExceptionalTailNumerics
                (ε1 := ε1) (ε2 := ε2) (d := (d : ℝ))
                (r := (r : ℝ)) (u := u)
                hε2 h30 hd_ge_98_real hr_nonneg hu_nonneg
                (le_of_lt hu_lt_one) hr_le_d_real hru_le_eps_d
            have hQ_eq :
                RealChooseTwo b + RealChooseTwo (D - b) =
                  RealChooseTwo ((d : ℝ) - u) + RealChooseTwo u := by
              rw [hDb_eq_u, hb_eq_d_sub_u]
            simpa [hT_real_eq, hQ_eq] using htail)
  · intro hlargeMass
    let M : ℝ := (1 + ε2) * b
    let y : ℝ := T - M
    let u : ℝ := D - b
    have hfactor_pos : 0 < 1 + ε2 := by
      linarith
    have hb_le_D : b ≤ D := by
      have hscaled : (1 + ε2) * b ≤ (1 + ε2) * D :=
        le_trans hlargeMass hTle
      exact le_of_mul_le_mul_left hscaled hfactor_pos
    have hy_nonneg : 0 ≤ y := by
      dsimp [y, M]
      linarith only [hlargeMass]
    have hu_nonneg : 0 ≤ u := by
      dsimp [u]
      linarith only [hb_le_D]
    have hy_le_stretched_u : y ≤ (1 + ε2) * u := by
      calc
        y = T - (1 + ε2) * b := by
          rfl
        _ ≤ (1 + ε2) * D - (1 + ε2) * b :=
          sub_le_sub_right hTle ((1 + ε2) * b)
        _ = (1 + ε2) * u := by
          dsimp [u]
          ring
    by_cases hy_ge_one : 1 ≤ y
    · have hmono_y :
          RealChooseTwo y ≤ RealChooseTwo ((1 + ε2) * u) :=
        hChoose_mono_on_one hy_ge_one hy_le_stretched_u
      have hsum_bu : b + u = D := by
        dsimp [u]
        ring
      have htwo :
          RealChooseTwo M + RealChooseTwo ((1 + ε2) * u) ≤
            (1 + 10 * ε2) * (RealChooseTwo b + RealChooseTwo u) := by
        simpa [M] using
          HugeOppositeProjectionTwoBlockStretch
            (ε := ε2) (D := D) (b := b) (u := u)
            hε2 hε2_le_one hD hb hu_nonneg hsum_bu
      have hQ_nonneg_u : 0 ≤ RealChooseTwo b + RealChooseTwo u := by
        change 0 ≤ RealChooseTwo b + RealChooseTwo (D - b)
        exact hPairMass_nonneg
      have htwo_eps :
          RealChooseTwo M + RealChooseTwo ((1 + ε2) * u) ≤
            (1 + ε1) * (RealChooseTwo b + RealChooseTwo u) :=
        have hfactor_mul :
            (1 + 10 * ε2) * (RealChooseTwo b + RealChooseTwo u) ≤
              (1 + ε1) * (RealChooseTwo b + RealChooseTwo u) :=
          mul_le_mul_of_nonneg_right hfactor10 hQ_nonneg_u
        le_trans htwo hfactor_mul
      have hleft_le :
          RealChooseTwo M + RealChooseTwo y ≤
            RealChooseTwo M + RealChooseTwo ((1 + ε2) * u) :=
        add_le_add (le_refl (RealChooseTwo M)) hmono_y
      change
        RealChooseTwo M + RealChooseTwo y ≤
          (1 + ε1) * (RealChooseTwo b + RealChooseTwo u)
      exact le_trans hleft_le htwo_eps
    · have hy_le_one : y ≤ 1 := le_of_not_ge hy_ge_one
      by_cases hregular : u = 0 ∨ 1 ≤ u
      · have hCy_nonpos : RealChooseTwo y ≤ 0 := by
          exact hChoose_nonpos_on_unit hy_nonneg hy_le_one
        have hM_regular :
            RealChooseTwo M ≤
              (1 + 10 * ε2) *
                (RealChooseTwo b + RealChooseTwo (D - b)) := by
          have hregular_D : D - b ≤ 0 ∨ 1 ≤ D - b := by
            rcases hregular with hu_eq_zero | hu_ge_one
            · left
              dsimp [u] at hu_eq_zero
              linarith
            · right
              simpa [u] using hu_ge_one
          simpa [M] using hstretchedB_regular hregular_D
        have hM_eps :
            RealChooseTwo M ≤
              (1 + ε1) *
                (RealChooseTwo b + RealChooseTwo (D - b)) :=
          have hfactor_mul :
              (1 + 10 * ε2) *
                  (RealChooseTwo b + RealChooseTwo (D - b)) ≤
                (1 + ε1) *
                  (RealChooseTwo b + RealChooseTwo (D - b)) :=
            mul_le_mul_of_nonneg_right hfactor10 hPairMass_nonneg
          le_trans hM_regular hfactor_mul
        have hleft_le : RealChooseTwo M + RealChooseTwo y ≤ RealChooseTwo M := by
          nlinarith only [hCy_nonpos]
        exact le_trans hleft_le hM_eps
      · have hu_pos : 0 < u := by
          by_contra hnot
          have hu_le_zero : u ≤ 0 := le_of_not_gt hnot
          have hu_eq_zero : u = 0 := le_antisymm hu_le_zero hu_nonneg
          exact hregular (Or.inl hu_eq_zero)
        have hu_lt_one : u < 1 := by
          by_contra hnot
          have hu_ge_one : 1 ≤ u := le_of_not_gt hnot
          exact hregular (Or.inr hu_ge_one)
        rcases hDnat with ⟨d, hD_eq⟩
        rcases hTnat with ⟨t, hT_eq⟩
        have hd_ge_98 : 98 ≤ d := by
          have hd_real : (98 : ℝ) ≤ d := by
            nlinarith [hD, hD_eq]
          exact_mod_cast hd_real
        have hd_ge_98_real : (98 : ℝ) ≤ d := by
          exact_mod_cast hd_ge_98
        have hd_nonneg_real : 0 ≤ (d : ℝ) := by
          linarith only [hd_ge_98_real]
        have hsum_bu_d : b + u = (d : ℝ) := by
          dsimp [u]
          rw [hD_eq]
          ring
        have hb_gt_d_minus_one : (d : ℝ) - 1 < b := by
          linarith only [hsum_bu_d, hu_lt_one]
        have hM_ge_b : b ≤ M := by
          dsimp [M]
          have hepsb_nonneg : 0 ≤ ε2 * b := mul_nonneg hε2 hb
          nlinarith only [hepsb_nonneg]
        have hM_gt_d_minus_one : (d : ℝ) - 1 < M :=
          lt_of_lt_of_le hb_gt_d_minus_one hM_ge_b
        have hd_le_t : d ≤ t := by
          by_contra hnot
          have ht_add_le_d : t + 1 ≤ d := by
            omega
          have ht_add_le_d_real : (t : ℝ) + 1 ≤ (d : ℝ) := by
            exact_mod_cast ht_add_le_d
          have hT_le_d_minus_one : T ≤ (d : ℝ) - 1 := by
            rw [hT_eq]
            linarith only [ht_add_le_d_real]
          linarith only [hM_gt_d_minus_one, hlargeMass, hT_le_d_minus_one]
        obtain ⟨r, ht_eq_d_add_r⟩ := Nat.exists_eq_add_of_le hd_le_t
        have ht_real_eq : (t : ℝ) = (d : ℝ) + (r : ℝ) := by
          exact_mod_cast ht_eq_d_add_r
        have hT_real_eq : T = (d : ℝ) + (r : ℝ) := by
          rw [hT_eq, ht_real_eq]
        have hT_le_stretched_d :
            (d : ℝ) + (r : ℝ) ≤ (1 + ε2) * (d : ℝ) := by
          calc
            (d : ℝ) + (r : ℝ) = T := by
              rw [hT_real_eq]
            _ ≤ (1 + ε2) * D := hTle
            _ = (1 + ε2) * (d : ℝ) := by
              rw [hD_eq]
        have hr_le_eps_d : (r : ℝ) ≤ ε2 * (d : ℝ) := by
          calc
            (r : ℝ) = ((d : ℝ) + (r : ℝ)) - (d : ℝ) := by
              ring
            _ ≤ (1 + ε2) * (d : ℝ) - (d : ℝ) :=
              sub_le_sub_right hT_le_stretched_d (d : ℝ)
            _ = ε2 * (d : ℝ) := by
              ring
        have hb_le_d_real : b ≤ (d : ℝ) := by
          linarith only [hsum_bu_d, hu_nonneg]
        have hepsd_nonneg : 0 ≤ ε2 * (d : ℝ) :=
          mul_nonneg hε2 hd_nonneg_real
        have hepsb_le_epsd : ε2 * b ≤ ε2 * (d : ℝ) :=
          mul_le_mul_of_nonneg_left hb_le_d_real hε2
        have hr_nonneg : 0 ≤ (r : ℝ) := by
          exact_mod_cast Nat.zero_le r
        have hyu_eq : y - u = (r : ℝ) - ε2 * b := by
          dsimp [y, M]
          rw [hT_real_eq]
          nlinarith only [hsum_bu_d]
        have hyu_upper : y - u ≤ 2 * ε2 * (d : ℝ) := by
          rw [hyu_eq]
          nlinarith only [hr_le_eps_d, hepsd_nonneg, hε2, hb]
        have hyu_lower : -(2 * ε2 * (d : ℝ)) ≤ y - u := by
          rw [hyu_eq]
          nlinarith only [hr_nonneg, hepsb_le_epsd, hepsd_nonneg]
        have hyu_abs : |y - u| ≤ 2 * ε2 * (d : ℝ) :=
          abs_le.mpr ⟨hyu_lower, hyu_upper⟩
        have hlarge_exceptional :=
          HugeOppositeProjectionLargeExceptionalNumerics
            (ε1 := ε1) (ε2 := ε2) (d := (d : ℝ))
            (b := b) (y := y) (u := u)
            hε1 hε2 hε2_le_one h30 hd_ge_98_real hb hy_nonneg hy_le_one
            hu_nonneg (le_of_lt hu_lt_one) hsum_bu_d hyu_abs
        change
          RealChooseTwo M + RealChooseTwo y ≤
            (1 + ε1) * (RealChooseTwo b + RealChooseTwo u)
        simpa [M] using hlarge_exceptional
