import Tablet.HugeFamilyFiniteUnionLowerBound
import Tablet.ProjectionDeficitFromSubset

-- [TABLET NODE: ProjectionDeficitFromUnionLoss]

theorem ProjectionDeficitFromUnionLoss :
    ∀ {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (H : Finset α) (I : Finset β) (A : α → Finset β)
      (f : β → γ) (k : ℕ) (δ C : ℝ),
      I.card = k →
      (∀ x, x ∈ H → A x ⊆ I) →
      (∀ x, x ∈ H → ∀ y, y ∈ H → x ≠ y →
        (((A x ∩ A y).card : ℝ) ≤ C)) →
      0 ≤ δ →
      RealChooseTwo (H.card : ℝ) * C ≤
        δ * H.sum (fun x => ((A x).card : ℝ)) →
      (((H.biUnion A).image f).card : ℝ) ≤
        δ * H.sum (fun x => ((A x).card : ℝ)) →
      (1 - 2 * δ) * H.sum (fun x => ((A x).card : ℝ)) ≤
        (k : ℝ) - ((I.image f).card : ℝ) := by
-- BODY
  classical
  intro α β γ _ _ _ H I A f k δ C hI hsubset hoverlap hδ
    hoverlapLoss himageLoss
  let W : Finset β := H.biUnion A
  have hW_subset : W ⊆ I := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨x, hx, hvx⟩
    exact hsubset x hx hvx
  have hdeficit_from_W :
      ((W.card : ℝ) - ((W.image f).card : ℝ)) ≤
        (k : ℝ) - ((I.image f).card : ℝ) :=
    ProjectionDeficitFromSubset I W f k hI hW_subset
  have hunion_lower :
      H.sum (fun x => ((A x).card : ℝ)) -
          RealChooseTwo (H.card : ℝ) * C
        ≤ (W.card : ℝ) := by
    simpa [W] using HugeFamilyFiniteUnionLowerBound H A C hoverlap
  simpa [W] using
    (by
      nlinarith only [hunion_lower, hdeficit_from_W, hoverlapLoss,
        himageLoss] :
        (1 - 2 * δ) * H.sum (fun x => ((A x).card : ℝ)) ≤
          (k : ℝ) - ((I.image f).card : ℝ))
