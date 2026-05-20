import Tablet.TwoBiteUnclosedProjectedPairs
import Tablet.TwoBiteTouchedProjectedPairs
import Tablet.TwoBiteStagedOpenPairs
import Tablet.TwoBiteProjectionPairSet
import Tablet.TwoBiteProjectionPairClosed
import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteProjectionPairTouched
import Tablet.TwoBitePreTerminalRecordedPairs
import Tablet.TwoBiteSameColorClosedImpliesClosed
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteX

-- [TABLET NODE: StagedOpenPairsFromUnclosedAndTouched]

theorem StagedOpenPairsFromUnclosedAndTouched :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (ε ε1 f : ℝ),
      f - 9 * ε1 * (I.card : ℝ) ^ 2 ≤
        ((TwoBiteUnclosedProjectedPairs ω I).card : ℝ) →
      ((TwoBiteTouchedProjectedPairs ω ε I).card : ℝ) ≤
        ε1 * (I.card : ℝ) ^ 2 →
      f - 10 * ε1 * (I.card : ℝ) ^ 2 ≤
        ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
-- BODY
  intro n m p ω I ε ε1 f hUnclosed hTouched
  classical
  let U := TwoBiteUnclosedProjectedPairs ω I
  let T := TwoBiteTouchedProjectedPairs ω ε I
  let O := TwoBiteStagedOpenPairs ω ε I
  have hsubset : U \ T ⊆ O := by
    intro e he
    have hrecorded_imp :
        e ∈ TwoBitePreTerminalRecordedPairs ω ε I →
          TwoBiteProjectionPairClosed ω I e ∨ TwoBiteProjectionPairTouched ω ε I e := by
      intro hrec
      cases e with
      | inl q =>
          simp [TwoBitePreTerminalRecordedPairs] at hrec
          rcases hrec with ⟨_hterm, hrec⟩
          rcases hrec with hincident | hx
          · right
            rcases hincident with ⟨r, s, hq, hcases⟩
            rcases hcases with hcase | hcase
            · rcases hcase with ⟨hr, _hs_cont⟩
              rcases hq with hq | hq
              · subst q
                exact Or.inl hr
              · subst q
                exact Or.inr hr
            · rcases hcase with ⟨hs, _hr_cont⟩
              rcases hq with hq | hq
              · subst q
                exact Or.inr hs
              · subst q
                exact Or.inl hs
          · left
            rcases hx with hx | hx
            · rcases hx with ⟨r, _hxrev, hxpair⟩
              exact ⟨Sum.inl r, hxpair⟩
            · rcases hx with ⟨b, _hxrev, hxpair⟩
              exact ⟨Sum.inr b, hxpair⟩
      | inr q =>
          simp [TwoBitePreTerminalRecordedPairs] at hrec
          rcases hrec with ⟨_hterm, hrec⟩
          rcases hrec with hincident | hx
          · right
            rcases hincident with ⟨b, c, hq, hcases⟩
            rcases hcases with hcase | hcase
            · rcases hcase with ⟨hb, _hc_cont⟩
              rcases hq with hq | hq
              · subst q
                exact Or.inl hb
              · subst q
                exact Or.inr hb
            · rcases hcase with ⟨hc, _hb_cont⟩
              rcases hq with hq | hq
              · subst q
                exact Or.inr hc
              · subst q
                exact Or.inl hc
          · left
            rcases hx with hx | hx
            · rcases hx with ⟨r, _hxrev, hxpair⟩
              exact ⟨Sum.inl r, hxpair⟩
            · rcases hx with ⟨b, _hxrev, hxpair⟩
              exact ⟨Sum.inr b, hxpair⟩
    simp [U, T, O, TwoBiteUnclosedProjectedPairs, TwoBiteTouchedProjectedPairs,
      TwoBiteStagedOpenPairs] at he ⊢
    rcases he with ⟨⟨hP, hnotClosed⟩, hnotTouchedOnP⟩
    refine ⟨hP, ?_, ?_, ?_⟩
    · intro hsame
      exact hnotClosed (TwoBiteSameColorClosedImpliesClosed ω I e hsame)
    · exact hnotTouchedOnP hP
    · intro hrec
      rcases hrecorded_imp hrec with hclosed | htouched
      · exact hnotClosed hclosed
      · exact (hnotTouchedOnP hP) htouched
  have houtside_le : ((U \ T).card : ℝ) ≤ (O.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hU_le : (U.card : ℝ) ≤ ((U \ T).card : ℝ) + (T.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s := U) (t := T))
  have hdiff_le : (U.card : ℝ) - (T.card : ℝ) ≤ (O.card : ℝ) := by
    nlinarith
  have hUnclosed' : f - 9 * ε1 * (I.card : ℝ) ^ 2 ≤ (U.card : ℝ) := by
    simpa [U] using hUnclosed
  have hTouched' : (T.card : ℝ) ≤ ε1 * (I.card : ℝ) ^ 2 := by
    simpa [T] using hTouched
  have hO : (O.card : ℝ) = ((TwoBiteStagedOpenPairs ω ε I).card : ℝ) := by
    simp [O]
  rw [← hO]
  nlinarith
