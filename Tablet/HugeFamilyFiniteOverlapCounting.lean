import Tablet.HugeFamilyFiniteUnionLowerBound
import Tablet.RealChooseTwo

-- [TABLET NODE: HugeFamilyFiniteOverlapCounting]

theorem HugeFamilyFiniteOverlapCounting :
    ∀ {α β : Type} [DecidableEq α] [DecidableEq β]
      (H : Finset α) (I : Finset β) (A : α → Finset β)
      (k : ℕ) (t C : ℝ),
      I.card = k →
      (∀ x, x ∈ H → A x ⊆ I) →
      (∀ x, x ∈ H → t < ((A x).card : ℝ) ∧ ((A x).card : ℝ) ≤ (k : ℝ)) →
      (∀ x, x ∈ H → ∀ y, y ∈ H → x ≠ y →
        (((A x ∩ A y).card : ℝ) ≤ C)) →
      0 < t →
      0 ≤ C →
      RealChooseTwo (2 * (k : ℝ) / t + 1) * C ≤ (1 / 2 : ℝ) * (k : ℝ) →
      H.sum (fun x => ((A x).card : ℝ)) ≤ 2 * (k : ℝ) ∧
        (H.card : ℝ) ≤ 2 * (k : ℝ) / t := by
-- BODY
  classical
  intro α β _ _ H I A k t C hI hsubset hbounds hoverlap ht hC hnumeric
  let a : ℝ := 2 * (k : ℝ) / t
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have ha_nonneg : 0 ≤ a := by
    exact div_nonneg (mul_nonneg (by norm_num) hk_nonneg) (le_of_lt ht)
  have hchoose_mono :
      ∀ {u v : ℝ}, 1 ≤ u → u ≤ v → RealChooseTwo u ≤ RealChooseTwo v := by
    intro u v hu huv
    unfold RealChooseTwo
    nlinarith only [hu, huv, sq_nonneg (v - u)]
  have hcard_bound : (H.card : ℝ) ≤ a := by
    by_contra hnot
    have hgt : a < (H.card : ℝ) := lt_of_not_ge hnot
    let r : ℕ := max 1 (Nat.ceil a)
    have hone_le_r : 1 ≤ r := by
      exact le_max_left 1 (Nat.ceil a)
    have ha_le_r : a ≤ (r : ℝ) := by
      have hceil_le_r : Nat.ceil a ≤ r := le_max_right 1 (Nat.ceil a)
      exact le_trans (Nat.le_ceil a) (by exact_mod_cast hceil_le_r)
    have hr_le_a1 : (r : ℝ) ≤ a + 1 := by
      change ((max 1 (Nat.ceil a) : ℕ) : ℝ) ≤ a + 1
      rw [Nat.cast_max]
      refine max_le ?_ ?_
      · norm_num
        exact ha_nonneg
      · exact le_of_lt (Nat.ceil_lt_add_one ha_nonneg)
    have hr_le_H : r ≤ H.card := by
      have hceil_le_H : Nat.ceil a ≤ H.card := Nat.ceil_le.mpr (le_of_lt hgt)
      have hH_pos_real : (0 : ℝ) < (H.card : ℝ) := lt_of_le_of_lt ha_nonneg hgt
      have hH_pos_nat : 0 < H.card := by exact_mod_cast hH_pos_real
      have h1_le_H : 1 ≤ H.card := Nat.succ_le_of_lt hH_pos_nat
      exact max_le h1_le_H hceil_le_H
    obtain ⟨B, hBH, hBcard⟩ := Finset.exists_subset_card_eq hr_le_H
    have hB_nonempty : B.Nonempty := by
      apply Finset.card_pos.mp
      rw [hBcard]
      exact lt_of_lt_of_le Nat.zero_lt_one hone_le_r
    have hsum_t_lt :
        B.sum (fun _ : α => t) < B.sum (fun x => ((A x).card : ℝ)) := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro x hx
        exact le_of_lt (hbounds x (hBH hx)).1
      · rcases hB_nonempty with ⟨x, hx⟩
        exact ⟨x, hx, (hbounds x (hBH hx)).1⟩
    have hsum_gt_rt :
        (r : ℝ) * t < B.sum (fun x => ((A x).card : ℝ)) := by
      have hconst : B.sum (fun _ : α => t) = (r : ℝ) * t := by
        simp [hBcard, nsmul_eq_mul]
      simpa [hconst] using hsum_t_lt
    have hrt_ge : 2 * (k : ℝ) ≤ (r : ℝ) * t := by
      have hmul := mul_le_mul_of_nonneg_right ha_le_r (le_of_lt ht)
      have ha_mul : a * t = 2 * (k : ℝ) := by
        simp [a]
        field_simp [ne_of_gt ht]
      linarith only [hmul, ha_mul]
    have hchoose_r_le :
        RealChooseTwo (r : ℝ) ≤ RealChooseTwo (a + 1) :=
      hchoose_mono (by exact_mod_cast hone_le_r) hr_le_a1
    have hchoose_rC_le :
        RealChooseTwo (r : ℝ) * C ≤ (1 / 2 : ℝ) * (k : ℝ) := by
      calc
        RealChooseTwo (r : ℝ) * C
            ≤ RealChooseTwo (a + 1) * C :=
              mul_le_mul_of_nonneg_right hchoose_r_le hC
        _ ≤ (1 / 2 : ℝ) * (k : ℝ) := by
          simpa [a] using hnumeric
    have hoverlap_B :
        ∀ x, x ∈ B → ∀ y, y ∈ B → x ≠ y →
          (((A x ∩ A y).card : ℝ) ≤ C) := by
      intro x hx y hy hxy
      exact hoverlap x (hBH hx) y (hBH hy) hxy
    have hlower :
        B.sum (fun x => ((A x).card : ℝ)) -
            RealChooseTwo (B.card : ℝ) * C
          ≤ ((B.biUnion A).card : ℝ) :=
      HugeFamilyFiniteUnionLowerBound B A C hoverlap_B
    have hunion_subset : B.biUnion A ⊆ I := by
      intro v hv
      rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨x, hx, hvx⟩
      exact hsubset x (hBH hx) hvx
    have hunion_le_k : ((B.biUnion A).card : ℝ) ≤ (k : ℝ) := by
      calc
        ((B.biUnion A).card : ℝ) ≤ (I.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hunion_subset
        _ = (k : ℝ) := by exact_mod_cast hI
    have hlower_gt :
        (3 / 2 : ℝ) * (k : ℝ) <
          B.sum (fun x => ((A x).card : ℝ)) -
            RealChooseTwo (B.card : ℝ) * C := by
      rw [hBcard]
      nlinarith only [hsum_gt_rt, hrt_ge, hchoose_rC_le]
    nlinarith only [hlower, hunion_le_k, hlower_gt, hk_nonneg]
  have hoverlap_H :
      H.sum (fun x => ((A x).card : ℝ)) -
          RealChooseTwo (H.card : ℝ) * C
        ≤ ((H.biUnion A).card : ℝ) :=
    HugeFamilyFiniteUnionLowerBound H A C hoverlap
  have hunion_H_subset : H.biUnion A ⊆ I := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨x, hx, hvx⟩
    exact hsubset x hx hvx
  have hunion_H_le_k : ((H.biUnion A).card : ℝ) ≤ (k : ℝ) := by
    calc
      ((H.biUnion A).card : ℝ) ≤ (I.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hunion_H_subset
      _ = (k : ℝ) := by exact_mod_cast hI
  have hchoose_HC_le : RealChooseTwo (H.card : ℝ) * C ≤ (1 / 2 : ℝ) * (k : ℝ) := by
    by_cases hHsmall : (H.card : ℝ) ≤ 1
    · have hchoose_nonpos : RealChooseTwo (H.card : ℝ) ≤ 0 := by
        unfold RealChooseTwo
        have hH_nonneg : 0 ≤ (H.card : ℝ) := by positivity
        nlinarith only [hH_nonneg, hHsmall]
      have hleft_nonpos : RealChooseTwo (H.card : ℝ) * C ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hchoose_nonpos hC
      have hright_nonneg : 0 ≤ (1 / 2 : ℝ) * (k : ℝ) := by positivity
      linarith only [hleft_nonpos, hright_nonneg]
    · have hH_ge_one : 1 ≤ (H.card : ℝ) := le_of_not_ge hHsmall
      have hH_le_a1 : (H.card : ℝ) ≤ a + 1 := by linarith only [hcard_bound]
      have hchoose_H_le :
          RealChooseTwo (H.card : ℝ) ≤ RealChooseTwo (a + 1) :=
        hchoose_mono hH_ge_one hH_le_a1
      calc
        RealChooseTwo (H.card : ℝ) * C
            ≤ RealChooseTwo (a + 1) * C :=
              mul_le_mul_of_nonneg_right hchoose_H_le hC
        _ ≤ (1 / 2 : ℝ) * (k : ℝ) := by
          simpa [a] using hnumeric
  have hsum_bound : H.sum (fun x => ((A x).card : ℝ)) ≤ 2 * (k : ℝ) := by
    nlinarith only [hoverlap_H, hunion_H_le_k, hchoose_HC_le, hk_nonneg]
  exact ⟨hsum_bound, hcard_bound⟩
