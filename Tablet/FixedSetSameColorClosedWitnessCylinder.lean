import Tablet.TwoBiteProjectionPairSameColorClosed
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteBasePairs
import Tablet.TwoBiteXPlus
import Tablet.TwoBiteLiftedPositiveNeighborhood

-- [TABLET NODE: FixedSetSameColorClosedWitnessCylinder]

theorem FixedSetSameColorClosedWitnessCylinder :
    ∀ {n m : ℕ} {p : ℝ} (ω ω' : TwoBiteSample n m p)
      (I : Finset (Fin n))
      (e : Sum (Fin m × Fin m) (Fin m × Fin m))
      (support : Finset (Sum (Fin m × Fin m) (Fin m × Fin m))),
      (∀ x : Fin n, ω.2.2 x = ω'.2.2 x) →
      (∀ c,
        c ∈ support →
          (TwoBiteEdgeCoordinateValue ω c ↔
            TwoBiteEdgeCoordinateValue ω' c)) →
      (match e with
        | Sum.inl q =>
            ∀ r : Fin m,
              r.val < q.1.val →
              r.val < q.2.val →
                Sum.inl (r, q.1) ∈ support ∧
                  Sum.inl (r, q.2) ∈ support
        | Sum.inr q =>
            ∀ b : Fin m,
              b.val < q.1.val →
              b.val < q.2.val →
                Sum.inr (b, q.1) ∈ support ∧
                  Sum.inr (b, q.2) ∈ support) →
        (TwoBiteProjectionPairSameColorClosed ω I e ↔
          TwoBiteProjectionPairSameColorClosed ω' I e) := by
-- BODY
  classical
  intro n m p ω ω' I e support hEmb hAgree hsupport
  cases e with
  | inl q =>
      dsimp [TwoBiteProjectionPairSameColorClosed] at hsupport ⊢
      have red_transfer :
          ∀ (Ω Ω' : TwoBiteSample n m p),
            (∀ x : Fin n, Ω.2.2 x = Ω'.2.2 x) →
            (∀ c,
              c ∈ support →
                (TwoBiteEdgeCoordinateValue Ω c ↔
                  TwoBiteEdgeCoordinateValue Ω' c)) →
            (∃ r : Fin m,
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteXPlus Ω I (Sum.inl r)).image
                    (TwoBiteRedProjection Ω))) →
              ∃ r : Fin m,
                q ∈
                  TwoBiteBasePairs
                    ((TwoBiteXPlus Ω' I (Sum.inl r)).image
                      (TwoBiteRedProjection Ω')) := by
        intro Ω Ω' hEmbΩ hAgreeΩ h
        rcases h with ⟨r, hq⟩
        refine ⟨r, ?_⟩
        simp [TwoBiteBasePairs, TwoBitePairsInSet, TwoBiteXPlus,
          TwoBiteLiftedPositiveNeighborhood, TwoBiteRedProjection,
          TwoBiteEmbedding] at hq ⊢
        rcases hq with ⟨⟨ha, hb⟩, hpair⟩
        rcases ha with ⟨a, ⟨haI, hra, hreda⟩, hproja⟩
        rcases hb with ⟨b, ⟨hbI, hrb, hredb⟩, hprojb⟩
        have hproja' : (Ω'.2.2 a).1 = q.1 := by
          simpa [← hEmbΩ a] using hproja
        have hprojb' : (Ω'.2.2 b).1 = q.2 := by
          simpa [← hEmbΩ b] using hprojb
        have hraq : r < q.1 := by
          simpa [hproja] using hra
        have hrbq : r < q.2 := by
          simpa [hprojb] using hrb
        have hsuppa : Sum.inl (r, q.1) ∈ support :=
          (hsupport r hraq hrbq).1
        have hsuppb : Sum.inl (r, q.2) ∈ support :=
          (hsupport r hraq hrbq).2
        have hreda_q : (TwoBiteRedGraph Ω).Adj r q.1 := by
          simpa [hproja] using hreda
        have hredb_q : (TwoBiteRedGraph Ω).Adj r q.2 := by
          simpa [hprojb] using hredb
        have hreda_q' : (TwoBiteRedGraph Ω').Adj r q.1 :=
          (hAgreeΩ (Sum.inl (r, q.1)) hsuppa).1 hreda_q
        have hredb_q' : (TwoBiteRedGraph Ω').Adj r q.2 :=
          (hAgreeΩ (Sum.inl (r, q.2)) hsuppb).1 hredb_q
        refine ⟨⟨?_, ?_⟩, hpair⟩
        · refine ⟨a, ⟨haI, ?_, ?_⟩, hproja'⟩
          · simpa [hproja'] using hraq
          · simpa [hproja'] using hreda_q'
        · refine ⟨b, ⟨hbI, ?_, ?_⟩, hprojb'⟩
          · simpa [hprojb'] using hrbq
          · simpa [hprojb'] using hredb_q'
      constructor
      · intro h
        exact red_transfer ω ω' hEmb hAgree h
      · intro h
        exact
          red_transfer ω' ω (fun x => (hEmb x).symm)
            (fun c hc => (hAgree c hc).symm) h
  | inr q =>
      dsimp [TwoBiteProjectionPairSameColorClosed] at hsupport ⊢
      have blue_transfer :
          ∀ (Ω Ω' : TwoBiteSample n m p),
            (∀ x : Fin n, Ω.2.2 x = Ω'.2.2 x) →
            (∀ c,
              c ∈ support →
                (TwoBiteEdgeCoordinateValue Ω c ↔
                  TwoBiteEdgeCoordinateValue Ω' c)) →
            (∃ b : Fin m,
              q ∈
                TwoBiteBasePairs
                  ((TwoBiteXPlus Ω I (Sum.inr b)).image
                    (TwoBiteBlueProjection Ω))) →
              ∃ b : Fin m,
                q ∈
                  TwoBiteBasePairs
                    ((TwoBiteXPlus Ω' I (Sum.inr b)).image
                      (TwoBiteBlueProjection Ω')) := by
        intro Ω Ω' hEmbΩ hAgreeΩ h
        rcases h with ⟨s, hq⟩
        refine ⟨s, ?_⟩
        simp [TwoBiteBasePairs, TwoBitePairsInSet, TwoBiteXPlus,
          TwoBiteLiftedPositiveNeighborhood, TwoBiteBlueProjection,
          TwoBiteEmbedding] at hq ⊢
        rcases hq with ⟨⟨ha, hb⟩, hpair⟩
        rcases ha with ⟨a, ⟨haI, hsa, hbluea⟩, hproja⟩
        rcases hb with ⟨b, ⟨hbI, hsb, hblueb⟩, hprojb⟩
        have hproja' : (Ω'.2.2 a).2 = q.1 := by
          simpa [← hEmbΩ a] using hproja
        have hprojb' : (Ω'.2.2 b).2 = q.2 := by
          simpa [← hEmbΩ b] using hprojb
        have hsaq : s < q.1 := by
          simpa [hproja] using hsa
        have hsbq : s < q.2 := by
          simpa [hprojb] using hsb
        have hsuppa : Sum.inr (s, q.1) ∈ support :=
          (hsupport s hsaq hsbq).1
        have hsuppb : Sum.inr (s, q.2) ∈ support :=
          (hsupport s hsaq hsbq).2
        have hbluea_q : (TwoBiteBlueGraph Ω).Adj s q.1 := by
          simpa [hproja] using hbluea
        have hblueb_q : (TwoBiteBlueGraph Ω).Adj s q.2 := by
          simpa [hprojb] using hblueb
        have hbluea_q' : (TwoBiteBlueGraph Ω').Adj s q.1 :=
          (hAgreeΩ (Sum.inr (s, q.1)) hsuppa).1 hbluea_q
        have hblueb_q' : (TwoBiteBlueGraph Ω').Adj s q.2 :=
          (hAgreeΩ (Sum.inr (s, q.2)) hsuppb).1 hblueb_q
        refine ⟨⟨?_, ?_⟩, hpair⟩
        · refine ⟨a, ⟨haI, ?_, ?_⟩, hproja'⟩
          · simpa [hproja'] using hsaq
          · simpa [hproja'] using hbluea_q'
        · refine ⟨b, ⟨hbI, ?_, ?_⟩, hprojb'⟩
          · simpa [hprojb'] using hsbq
          · simpa [hprojb'] using hblueb_q'
      constructor
      · intro h
        exact blue_transfer ω ω' hEmb hAgree h
      · intro h
        exact
          blue_transfer ω' ω (fun x => (hEmb x).symm)
            (fun c hc => (hAgree c hc).symm) h
