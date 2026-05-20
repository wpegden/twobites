import Tablet.Preamble

-- [TABLET NODE: FixedSetHistoryCellRedTermwiseCylinderDomination]

theorem FixedSetHistoryCellRedTermwiseCylinderDomination :
    ∀ {Coord : Type} [DecidableEq Coord]
      {uR uB : ℕ} {p a residualMass : ℝ}
      (B R P A Z : Finset Coord),
      0 ≤ p →
      p ≤ (1 / 2 : ℝ) →
      0 ≤ residualMass →
      B.card = uB →
      R.card = uR →
      B ⊆ P →
      R ⊆ P →
      Disjoint B R →
      Z ⊆ A →
      Disjoint P A →
      max 0 (a - (uR : ℝ) - (uB : ℝ)) ≤ ((Z.card : ℝ)) →
      p ^ (P.card - uR - uB) *
          ((1 : ℝ) - p) ^ (A.card - Z.card) ≤ residualMass →
      p ^ P.card * ((1 : ℝ) - p) ^ A.card
        ≤
        p ^ uR * p ^ uB *
            Real.rpow ((1 : ℝ) - p)
              (max 0 (a - (uR : ℝ) - (uB : ℝ))) *
          residualMass := by
-- BODY
  intro Coord _ uR uB p a residualMass B R P A Z hp hp_half h_res_nonneg h_B_card h_R_card h_B_P h_R_P h_disj_BR h_Z_A h_disj_PA h_L h_res

  have hq_pos : 0 < (1 : ℝ) - p := by linarith
  have hq_le : (1 : ℝ) - p ≤ 1 := by linarith

  have h_BR_card : (B ∪ R).card = uB + uR := by
    rw [Finset.card_union_of_disjoint h_disj_BR, h_B_card, h_R_card]
  
  have h_BR_P : B ∪ R ⊆ P := Finset.union_subset h_B_P h_R_P
  have h_card_BR_P : (B ∪ R).card ≤ P.card := Finset.card_le_card h_BR_P
  rw [h_BR_card] at h_card_BR_P
  have h_uR_uB_le_P : uR + uB ≤ P.card := by omega

  have h_Z_card_le_A_card : Z.card ≤ A.card := Finset.card_le_card h_Z_A

  have hp_pow : p ^ P.card = p ^ uR * p ^ uB * p ^ (P.card - uR - uB) := by
    calc p ^ P.card = p ^ (uR + uB + (P.card - uR - uB)) := by congr 1; omega
         _ = p ^ (uR + uB) * p ^ (P.card - uR - uB) := by rw [pow_add]
         _ = p ^ uR * p ^ uB * p ^ (P.card - uR - uB) := by rw [pow_add]

  have hq_pow : ((1 : ℝ) - p) ^ A.card = ((1 : ℝ) - p) ^ Z.card * ((1 : ℝ) - p) ^ (A.card - Z.card) := by
    calc ((1 : ℝ) - p) ^ A.card = ((1 : ℝ) - p) ^ (Z.card + (A.card - Z.card)) := by congr 1; omega
         _ = ((1 : ℝ) - p) ^ Z.card * ((1 : ℝ) - p) ^ (A.card - Z.card) := by rw [pow_add]

  have hq_Z_rpow : ((1 : ℝ) - p) ^ Z.card = Real.rpow ((1 : ℝ) - p) (Z.card : ℝ) :=
    (Real.rpow_natCast ((1 : ℝ) - p) Z.card).symm

  have hq_rpow_le : Real.rpow ((1 : ℝ) - p) (Z.card : ℝ) ≤ Real.rpow ((1 : ℝ) - p) (max 0 (a - uR - uB)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hq_pos hq_le h_L
    
  have h_pos_pow_p : 0 ≤ p ^ uR * p ^ uB := by positivity

  calc
    p ^ P.card * ((1 : ℝ) - p) ^ A.card
      = (p ^ uR * p ^ uB * p ^ (P.card - uR - uB)) * (((1 : ℝ) - p) ^ Z.card * ((1 : ℝ) - p) ^ (A.card - Z.card)) := by rw [hp_pow, hq_pow]
    _ = p ^ uR * p ^ uB * ((1 : ℝ) - p) ^ Z.card * (p ^ (P.card - uR - uB) * ((1 : ℝ) - p) ^ (A.card - Z.card)) := by ring
    _ ≤ p ^ uR * p ^ uB * ((1 : ℝ) - p) ^ Z.card * residualMass := by
        gcongr
    _ = p ^ uR * p ^ uB * Real.rpow ((1 : ℝ) - p) (Z.card : ℝ) * residualMass := by
        rw [hq_Z_rpow]
    _ ≤ p ^ uR * p ^ uB * Real.rpow ((1 : ℝ) - p) (max 0 (a - uR - uB)) * residualMass := by
        gcongr
