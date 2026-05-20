import Tablet.ProjectionDeficitFromUnionLoss

-- [TABLET NODE: ProjectionDeficitFromHugeFamilyEstimates]

theorem ProjectionDeficitFromHugeFamilyEstimates :
    ∀ {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (H : Finset α) (I : Finset β) (A : α → Finset β)
      (f : β → γ) (k : ℕ) (δ t C : ℝ),
      I.card = k →
      (∀ x, x ∈ H → A x ⊆ I) →
      (∀ x, x ∈ H → t ≤ ((A x).card : ℝ)) →
      (∀ x, x ∈ H → ∀ y, y ∈ H → x ≠ y →
        (((A x ∩ A y).card : ℝ) ≤ C)) →
      0 ≤ δ →
      0 ≤ C →
      (H.card : ℝ) ≤ 2 * (k : ℝ) / t →
      (2 * (k : ℝ) / t + 1) * C ≤ δ * t →
      (∀ x, x ∈ H →
        ((((A x).image f).card : ℝ) ≤ δ * ((A x).card : ℝ))) →
      (1 - 2 * δ) * H.sum (fun x => ((A x).card : ℝ)) ≤
        (k : ℝ) - ((I.image f).card : ℝ) := by
-- BODY
  classical
  intro α β γ _ _ _ H I A f k δ t C hI hsubset hsize hoverlap hδ
    hC hcard_bound hloss_scale himage_point
  have hsource_lower :
      (H.card : ℝ) * t ≤ H.sum (fun x => ((A x).card : ℝ)) := by
    calc
      (H.card : ℝ) * t = H.sum (fun _ => t) := by
        simp [nsmul_eq_mul]
      _ ≤ H.sum (fun x => ((A x).card : ℝ)) := by
        exact Finset.sum_le_sum hsize
  have hoverlapLoss :
      RealChooseTwo (H.card : ℝ) * C ≤
        δ * H.sum (fun x => ((A x).card : ℝ)) := by
    have hcard_nonneg : 0 ≤ (H.card : ℝ) := by positivity
    have hchoose_le :
        RealChooseTwo (H.card : ℝ) ≤
          (H.card : ℝ) * (2 * (k : ℝ) / t + 1) := by
      unfold RealChooseTwo
      nlinarith only [hcard_nonneg, hcard_bound]
    have hloss_le_card :
        RealChooseTwo (H.card : ℝ) * C ≤
          (H.card : ℝ) * ((2 * (k : ℝ) / t + 1) * C) := by
      calc
        RealChooseTwo (H.card : ℝ) * C ≤
            ((H.card : ℝ) * (2 * (k : ℝ) / t + 1)) * C :=
          mul_le_mul_of_nonneg_right hchoose_le hC
        _ = (H.card : ℝ) * ((2 * (k : ℝ) / t + 1) * C) := by
          ring
    have hcard_loss_le :
        (H.card : ℝ) * ((2 * (k : ℝ) / t + 1) * C) ≤
          (H.card : ℝ) * (δ * t) :=
      mul_le_mul_of_nonneg_left hloss_scale hcard_nonneg
    have hcard_delta_t_le :
        (H.card : ℝ) * (δ * t) ≤
          δ * H.sum (fun x => ((A x).card : ℝ)) := by
      calc
        (H.card : ℝ) * (δ * t) =
            δ * ((H.card : ℝ) * t) := by
          ring
        _ ≤ δ * H.sum (fun x => ((A x).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsource_lower hδ
    exact le_trans hloss_le_card (le_trans hcard_loss_le hcard_delta_t_le)
  have himageLoss :
      ((((H.biUnion A).image f).card : ℝ) ≤
        δ * H.sum (fun x => ((A x).card : ℝ))) := by
    have himage_subset :
        (H.biUnion A).image f ⊆ H.biUnion (fun x => (A x).image f) := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
      rw [Finset.mem_biUnion] at hv
      rcases hv with ⟨x, hx, hvx⟩
      rw [Finset.mem_biUnion]
      exact ⟨x, hx, Finset.mem_image.mpr ⟨v, hvx, rfl⟩⟩
    have hcard_image_union :
        ((((H.biUnion A).image f).card : ℝ) ≤
          ((H.biUnion (fun x => (A x).image f)).card : ℝ)) := by
      exact_mod_cast Finset.card_le_card himage_subset
    have hbi_card :
        (((H.biUnion (fun x => (A x).image f)).card : ℝ) ≤
          H.sum (fun x => (((A x).image f).card : ℝ))) := by
      exact_mod_cast
        (Finset.card_biUnion_le (s := H) (t := fun x => (A x).image f))
    have hsum_le :
        H.sum (fun x => (((A x).image f).card : ℝ)) ≤
          H.sum (fun x => δ * ((A x).card : ℝ)) :=
      Finset.sum_le_sum himage_point
    calc
      (((H.biUnion A).image f).card : ℝ) ≤
          ((H.biUnion (fun x => (A x).image f)).card : ℝ) :=
        hcard_image_union
      _ ≤ H.sum (fun x => (((A x).image f).card : ℝ)) := hbi_card
      _ ≤ H.sum (fun x => δ * ((A x).card : ℝ)) := hsum_le
      _ = δ * H.sum (fun x => ((A x).card : ℝ)) := by
        rw [← Finset.mul_sum]
  exact
    ProjectionDeficitFromUnionLoss H I A f k δ C hI hsubset hoverlap hδ
      hoverlapLoss himageLoss
