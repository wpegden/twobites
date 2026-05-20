import Tablet.Preamble
import Mathlib.Data.Fintype.Perm
import Tablet.MajorizationDiscrepancyTransfer
import Tablet.MajorizationTransferPrefixDominance
import Tablet.MajorizationTransferConvexCombination
import Tablet.MajorizationResortingDistance
import Tablet.FinVectorHasSortedPermutation

open Finset Real Equiv Equiv.Perm

-- [TABLET NODE: MajorizationFiniteDescent]

theorem MajorizationFiniteDescent :
    ∀ N : ℕ, ∀ b x : Fin N → ℝ,
    (∀ i : Fin N, ∃ k : ℕ, b i = k) →
    (∀ i : Fin N, ∃ k : ℕ, x i = k) →
    (∑ i, x i) = (∑ i, b i) →
    (∀ i j : Fin N, i.val ≤ j.val → b j ≤ b i) →
    (∀ i j : Fin N, i.val ≤ j.val → x j ≤ x i) →
    (∀ r : ℕ, r ≤ N →
      ∑ i ∈ univ.filter (·.val < r), b i ≤ ∑ i ∈ univ.filter (·.val < r), x i) →
    ∀ h : (Fin N → ℝ) → ℝ,
    (∀ y z : Fin N → ℝ, ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      h (fun i => (1 - θ) * y i + θ * z i) ≤ (1 - θ) * h y + θ * h z) →
    (∀ y : Fin N → ℝ, ∀ σ : Perm (Fin N), h (fun i => y (σ i)) = h y) →
    h b ≤ h x := by
-- BODY
  intro N b x hb hx h_sum h_b_mon h_mon h_pref h h_conv h_symm
  let dist_nat (x' : Fin N → ℝ) (hx' : ∀ i : Fin N, ∃ k : ℕ, x' i = k) : ℕ :=
    ∑ i : Fin N, ((Classical.choose (hx' i) : ℕ) - (Classical.choose (hb i) : ℕ) : ℤ).natAbs
  have h_dist_nat_eq : ∀ x' hx', (dist_nat x' hx' : ℝ) = ∑ i : Fin N, |x' i - b i| := by
    intro x' hx'
    dsimp [dist_nat]
    push_cast
    apply sum_congr rfl
    intro i _
    have hxi := Classical.choose_spec (hx' i)
    have hbi := Classical.choose_spec (hb i)
    rw [Nat.cast_natAbs]
    push_cast
    rw [← hxi, ← hbi]
  generalize hd : dist_nat x hx = D
  revert x hx h_sum h_mon h_pref hd
  induction D using Nat.strongRecOn with
  | ind D ih =>
    intro x hx h_sum h_mon h_pref hd_eq
    by_cases h_eq : x = b
    · rw [h_eq]
    · rcases MajorizationDiscrepancyTransfer N b x hb hx h_sum h_b_mon h_pref h_eq with ⟨i, j, hij, hbi, hxj, δ, hδ_pos, hδ_i, hδ_j, hr_mid⟩
      let y := fun (k : Fin N) => if k = i then x i - (δ:ℝ) else if k = j then x j + (δ:ℝ) else x k
      have hy_i : y i = x i - (δ:ℝ) := by simp [y]
      have hy_j : y j = x j + (δ:ℝ) := by
        have : j ≠ i := ne_of_gt hij
        simp [y, this]
      have hy_k : ∀ k, k ≠ i → k ≠ j → y k = x k := by
        intro k hki hkj
        simp [y, hki, hkj]
      have hy_int : ∀ k : Fin N, ∃ m : ℕ, y k = m := by
        intro k
        by_cases hki : k = i
        · rw [hki, hy_i]
          rcases hx i with ⟨xi_nat, hxi_nat⟩
          use xi_nat - δ
          rw [hxi_nat]
          have hδ_le : (δ:ℝ) ≤ xi_nat := by
            have hb_i := hb i
            rcases hb_i with ⟨bi_nat, hbi_nat⟩
            rw [hbi_nat] at hδ_i
            linarith
          have hδ_le_nat : δ ≤ xi_nat := Nat.cast_le.mp hδ_le
          push_cast
          exact (Nat.cast_sub hδ_le_nat).symm
        · by_cases hkj : k = j
          · rw [hkj, hy_j]
            rcases hx j with ⟨xj_nat, hxj_nat⟩
            use xj_nat + δ
            rw [hxj_nat]
            push_cast
            rfl
          · rw [hy_k k hki hkj]
            exact hx k
      have hd_pos_real : (0:ℝ) < δ := Nat.cast_pos.mpr hδ_pos
      have h_pref_dom := MajorizationTransferPrefixDominance N b x i j hij δ hd_pos_real hδ_i hδ_j hr_mid h_pref h_sum y hy_i hy_j hy_k
      rcases h_pref_dom with ⟨hy_sum, hy_pref⟩
      have hbi_xj : b j ≤ b i := h_b_mon i j (le_of_lt hij)
      have h_conv_comb := MajorizationTransferConvexCombination N b x y i j hij hbi_xj hbi hxj δ hd_pos_real hδ_i hδ_j hy_i hy_j hy_k
      rcases h_conv_comb with ⟨θ, hθ_nonneg, hθ_le_one, hy_eq_conv⟩
      have hy_le_hx : h y ≤ h x := by
        calc h y = h (fun k => (1 - θ) * x k + θ * x (swap i j k)) := by
              congr
              ext k
              exact hy_eq_conv k
          _ ≤ (1 - θ) * h x + θ * h (fun k => x (swap i j k)) := h_conv x (fun k => x (swap i j k)) θ hθ_nonneg hθ_le_one
          _ = (1 - θ) * h x + θ * h x := by
              rw [h_symm x (swap i j)]
          _ = h x := by ring
      rcases FinVectorHasSortedPermutation N y with ⟨y_down, ⟨σ, hy_down_perm⟩, hy_down_mon⟩
      have hy_down_int : ∀ k : Fin N, ∃ m : ℕ, y_down k = m := by
        intro k
        rw [hy_down_perm k]
        exact hy_int (σ k)
      have hd_y_down_le_y : ∑ k, |y_down k - b k| ≤ ∑ k, |y k - b k| := MajorizationResortingDistance N b y y_down h_b_mon hy_down_mon ⟨σ, hy_down_perm⟩
      have h_y_dist_eq : ∑ k, |y k - b k| = ∑ k, |x k - b k| - 2 * (δ:ℝ) := by
        have sum_eq : ∀ k, |y k - b k| = |x k - b k| - (if k = i then (δ:ℝ) else 0) - (if k = j then (δ:ℝ) else 0) := by
          intro k
          by_cases hki : k = i
          · rw [hki, hy_i]
            have hji : j ≠ i := ne_of_gt hij
            rw [if_pos rfl, if_neg hji.symm]
            have h1 : 0 ≤ x i - b i := by linarith
            have h2 : 0 ≤ x i - (δ:ℝ) - b i := by linarith
            rw [abs_of_nonneg h1, abs_of_nonneg h2]
            ring
          · by_cases hkj : k = j
            · rw [hkj, hy_j]
              have hji : j ≠ i := ne_of_gt hij
              rw [if_pos rfl, if_neg hji]
              have h1 : x j - b j ≤ 0 := by linarith
              have h2 : x j + (δ:ℝ) - b j ≤ 0 := by linarith
              rw [abs_of_nonpos h1, abs_of_nonpos h2]
              ring
            · rw [hy_k k hki hkj, if_neg hki, if_neg hkj]
              ring
        have h_sum_sub := sum_congr (s₂ := univ) rfl (fun k _ => sum_eq k)
        rw [h_sum_sub, sum_sub_distrib, sum_sub_distrib]
        have eq1 : ∑ k : Fin N, (if k = i then (δ:ℝ) else 0) = (δ:ℝ) := by
          rw [sum_ite_eq']
          exact if_pos (mem_univ i)
        have eq2 : ∑ k : Fin N, (if k = j then (δ:ℝ) else 0) = (δ:ℝ) := by
          rw [sum_ite_eq']
          exact if_pos (mem_univ j)
        rw [eq1, eq2]
        ring
      have hy_down_sum : ∑ k, y_down k = ∑ k, b k := by
        calc ∑ k, y_down k = ∑ k, y (σ k) := sum_congr rfl (fun k _ => hy_down_perm k)
          _ = ∑ k, y k := Equiv.sum_comp σ y
          _ = ∑ k, b k := hy_sum
      have hy_down_pref : ∀ r : ℕ, r ≤ N → ∑ i ∈ univ.filter (·.val < r), b i ≤ ∑ i ∈ univ.filter (·.val < r), y_down i := by
        intro r hr_le
        let F := univ.filter (fun (i : Fin N) => i.val < r)
        have hF_card : F.card = r := by
          have h_card : F.card = Fintype.card F := (Fintype.card_coe F).symm
          have e : F ≃ Fin r :=
            { toFun := fun x => ⟨x.val.val, by
                have hx := x.prop
                simp only [F, mem_filter, mem_univ, true_and] at hx
                exact hx⟩
              invFun := fun k => ⟨⟨k.val, by omega⟩, by simp [F, k.isLt]⟩
              left_inv := fun ⟨k, hk⟩ => Subtype.ext (Fin.ext rfl)
              right_inv := fun k => Fin.ext rfl }
          rw [h_card, Fintype.card_congr e, Fintype.card_fin]
        have h_b_le_y := hy_pref r hr_le
        have h_y_le_ydown : ∑ i ∈ F, y i ≤ ∑ i ∈ F, y_down i := by
          let T := F.image σ.symm
          have hT_card : T.card = r := by
            rw [card_image_of_injective F σ.symm.injective]
            exact hF_card
          have hT_sum : ∑ i ∈ T, y_down i = ∑ i ∈ F, y i := by
            calc ∑ i ∈ T, y_down i = ∑ i ∈ F.image σ.symm, y_down i := rfl
              _ = ∑ i ∈ F, y_down (σ.symm i) := sum_image (fun x _ y _ h_eq => σ.symm.injective h_eq)
              _ = ∑ i ∈ F, y i := sum_congr rfl (fun k _ => by
                have h_σ := hy_down_perm (σ.symm k)
                have heq : σ (σ.symm k) = k := Equiv.apply_symm_apply σ k
                rw [heq] at h_σ
                exact h_σ)
          rw [← hT_sum]
          have hdT : Disjoint (T \ F) (T ∩ F) := disjoint_sdiff_inter T F
          have hdF : Disjoint (F \ T) (F ∩ T) := disjoint_sdiff_inter F T
          have h_T_eq : ∑ i ∈ T, y_down i = ∑ i ∈ T \ F, y_down i + ∑ i ∈ T ∩ F, y_down i :=
            (congrArg (fun s => ∑ i ∈ s, y_down i) (sdiff_union_inter T F).symm).trans (sum_union hdT)
          have h_F_eq : ∑ i ∈ F, y_down i = ∑ i ∈ F \ T, y_down i + ∑ i ∈ F ∩ T, y_down i :=
            (congrArg (fun s => ∑ i ∈ s, y_down i) (sdiff_union_inter F T).symm).trans (sum_union hdF)
          rw [h_T_eq, h_F_eq, inter_comm F T]
          have h_add : ∀ X Y Z : ℝ, X ≤ Z → X + Y ≤ Z + Y := fun X Y Z h => add_le_add h (le_refl Y)
          apply h_add
          rcases eq_or_lt_of_le (Nat.zero_le r) with rfl | hrpos
          · have : T = ∅ := card_eq_zero.mp hT_card
            have hF_empty : F = ∅ := card_eq_zero.mp hF_card
            simp [this, hF_empty]
          · let pivot_idx : Fin N := ⟨r - 1, by omega⟩
            let pivot := y_down pivot_idx
            have hT_F_eq : (T \ F).card = (F \ T).card := by
              have h1 : (T \ F).card + (T ∩ F).card = T.card :=
                (card_union_of_disjoint hdT).symm.trans (congrArg card (sdiff_union_inter T F))
              have h2 : (F \ T).card + (F ∩ T).card = F.card :=
                (card_union_of_disjoint hdF).symm.trans (congrArg card (sdiff_union_inter F T))
              rw [inter_comm] at h2
              omega
            calc ∑ i ∈ T \ F, y_down i ≤ ∑ i ∈ T \ F, pivot := by
                  apply sum_le_sum
                  intro k hk
                  have : r ≤ k.val := by
                    have : k ∉ F := (mem_sdiff.mp hk).2
                    simp only [F, mem_filter, mem_univ, true_and, not_lt] at this
                    exact this
                  have : pivot_idx.val ≤ k.val := by
                    have hp : pivot_idx.val = r - 1 := rfl
                    omega
                  exact hy_down_mon pivot_idx k this
              _ = (T \ F).card * pivot := by simp only [sum_const, nsmul_eq_mul]
              _ = (F \ T).card * pivot := by rw [hT_F_eq]
              _ = ∑ j ∈ F \ T, pivot := by simp only [sum_const, nsmul_eq_mul]
              _ ≤ ∑ j ∈ F \ T, y_down j := by
                  apply sum_le_sum
                  intro k hk
                  have : k.val < r := by
                    have : k ∈ F := (mem_sdiff.mp hk).1
                    simp only [F, mem_filter, mem_univ, true_and] at this
                    exact this
                  have : k.val ≤ pivot_idx.val := by
                    have hp : pivot_idx.val = r - 1 := rfl
                    omega
                  exact hy_down_mon k pivot_idx this
        exact le_trans h_b_le_y h_y_le_ydown
      have hd_y_down_dist : dist_nat y_down hy_down_int < D := by
        have hd_D : (D:ℝ) = ∑ k, |x k - b k| := by
          rw [← hd_eq, h_dist_nat_eq]
        have hy_down_eq : (dist_nat y_down hy_down_int : ℝ) = ∑ k, |y_down k - b k| := h_dist_nat_eq y_down hy_down_int
        have h_le : ∑ k, |y_down k - b k| ≤ ∑ k, |x k - b k| - 2 * (δ:ℝ) := by
          linarith [hd_y_down_le_y, h_y_dist_eq]
        have h_lt : ∑ k, |y_down k - b k| < ∑ k, |x k - b k| := by
          linarith [hd_pos_real]
        rw [← hd_D, ← hy_down_eq] at h_lt
        exact_mod_cast h_lt
      have h_ind := ih (dist_nat y_down hy_down_int) hd_y_down_dist y_down hy_down_int hy_down_sum hy_down_mon hy_down_pref rfl
      calc h b ≤ h y_down := h_ind
        _ = h y := by
          have h_symm_y := h_symm y σ
          have : h (fun k => y (σ k)) = h y_down := by
            congr
            ext k
            exact (hy_down_perm k).symm
          rw [this] at h_symm_y
          exact h_symm_y
        _ ≤ h x := hy_le_hx
