import Tablet.TwoBiteProjectedPairsClosedInClass
import Tablet.TwoBiteClosedPairsInClass

-- [TABLET NODE: ProjectedPairsInClassMultiplicityBound]

theorem ProjectedPairsInClassMultiplicityBound :
    ∀ {n m : ℕ} {p : ℝ} (ω : TwoBiteSample n m p)
      (I : Finset (Fin n)) (cls : TwoBiteBaseVertex m → Prop),
      ((TwoBiteProjectedPairsClosedInClass ω I cls).card : ℝ) ≤
        2 * ((TwoBiteClosedPairsInClass ω I cls).card : ℝ) := by
-- BODY
  classical
  intro n m p ω I cls
  let A : Finset (TwoBiteBaseVertex m) :=
    (Finset.univ : Finset (TwoBiteBaseVertex m)).filter cls
  let Q : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)) :=
    TwoBiteProjectedPairsClosedInClass ω I cls
  let Fcls : Finset (Fin n × Fin n) :=
    TwoBiteClosedPairsInClass ω I cls
  have hProjectedPair_has_final_pair :
      ∀ (proj : Fin n → Fin m) (X : Finset (Fin n)) (q : Fin m × Fin m),
        q ∈ TwoBiteBasePairs (X.image proj) →
          ∃ a : Fin n × Fin n,
            a ∈ TwoBiteFinalPairs X ∧
              ((proj a.1 = q.1 ∧ proj a.2 = q.2) ∨
                (proj a.1 = q.2 ∧ proj a.2 = q.1)) := by
    intro proj X q hq
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq
    rcases hq with ⟨⟨hq1, hq2⟩, hqrank⟩
    rcases hq1 with ⟨u, huX, huproj⟩
    rcases hq2 with ⟨v, hvX, hvproj⟩
    have huv_ne : u ≠ v := by
      intro huv
      have hqeq : q.1 = q.2 := by
        calc
          q.1 = proj u := huproj.symm
          _ = proj v := by rw [huv]
          _ = q.2 := hvproj
      rw [hqeq] at hqrank
      exact (lt_irrefl q.2) hqrank
    by_cases huv_rank : u.val < v.val
    · refine ⟨(u, v), ?_, Or.inl ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, huX, hvX] using huv_rank
      · exact ⟨huproj, hvproj⟩
    · have hval_ne : u.val ≠ v.val := by
        intro hval
        exact huv_ne (Fin.ext hval)
      have hvu_rank : v.val < u.val := by
        have hle : v.val ≤ u.val := Nat.le_of_not_gt huv_rank
        exact lt_of_le_of_ne hle (Ne.symm hval_ne)
      refine ⟨(v, u), ?_, Or.inr ?_⟩
      · simpa [TwoBiteFinalPairs, TwoBitePairsInSet, hvX, huX] using hvu_rank
      · exact ⟨hvproj, huproj⟩
  have hQ_mem_cases :
      ∀ e, e ∈ Q →
        match e with
        | Sum.inl q =>
            ∃ x : TwoBiteBaseVertex m,
              x ∈ A ∧
                q ∈ TwoBiteBasePairs
                  ((TwoBiteX ω I x).image (TwoBiteRedProjection ω))
        | Sum.inr q =>
            ∃ x : TwoBiteBaseVertex m,
              x ∈ A ∧
                q ∈ TwoBiteBasePairs
                  ((TwoBiteX ω I x).image (TwoBiteBlueProjection ω)) := by
    intro e he
    dsimp [Q, TwoBiteProjectedPairsClosedInClass] at he
    rw [Finset.mem_filter] at he
    rcases he with ⟨_heProjection, heWitness⟩
    cases e with
    | inl q =>
        rcases heWitness with ⟨x, hcls, hq⟩
        have hxA : x ∈ A := by
          simp [A, hcls]
        exact ⟨x, hxA, hq⟩
    | inr q =>
        rcases heWitness with ⟨x, hcls, hq⟩
        have hxA : x ∈ A := by
          simp [A, hcls]
        exact ⟨x, hxA, hq⟩
  have hClosed_mem_of_witness :
      ∀ x : TwoBiteBaseVertex m, x ∈ A →
        ∀ a : Fin n × Fin n,
          a ∈ TwoBiteFinalPairs (TwoBiteX ω I x) → a ∈ Fcls := by
    intro x hxA a ha
    dsimp [Fcls, TwoBiteClosedPairsInClass]
    rw [Finset.mem_biUnion]
    have hcls : cls x := by
      simpa [A] using hxA
    exact ⟨x, by simp [hcls], ha⟩
  have hQ_has_final_witness :
      ∀ e, e ∈ Q →
        ∃ a : Fin n × Fin n,
          a ∈ Fcls ∧
            match e with
            | Sum.inl q =>
                ((TwoBiteRedProjection ω a.1 = q.1 ∧
                    TwoBiteRedProjection ω a.2 = q.2) ∨
                  (TwoBiteRedProjection ω a.1 = q.2 ∧
                    TwoBiteRedProjection ω a.2 = q.1))
            | Sum.inr q =>
                ((TwoBiteBlueProjection ω a.1 = q.1 ∧
                    TwoBiteBlueProjection ω a.2 = q.2) ∨
                  (TwoBiteBlueProjection ω a.1 = q.2 ∧
                    TwoBiteBlueProjection ω a.2 = q.1)) := by
    intro e he
    cases e with
    | inl q =>
        rcases hQ_mem_cases (Sum.inl q) he with ⟨x, hxA, hq⟩
        rcases hProjectedPair_has_final_pair (TwoBiteRedProjection ω)
            (TwoBiteX ω I x) q hq with ⟨a, haFinal, hproj⟩
        exact ⟨a, hClosed_mem_of_witness x hxA a haFinal, hproj⟩
    | inr q =>
        rcases hQ_mem_cases (Sum.inr q) he with ⟨x, hxA, hq⟩
        rcases hProjectedPair_has_final_pair (TwoBiteBlueProjection ω)
            (TwoBiteX ω I x) q hq with ⟨a, haFinal, hproj⟩
        exact ⟨a, hClosed_mem_of_witness x hxA a haFinal, hproj⟩
  have hProjectedPair_unique_for_final_pair :
      ∀ (proj : Fin n → Fin m) (X Y : Finset (Fin n)) (a : Fin n × Fin n)
        (q r : Fin m × Fin m),
        q ∈ TwoBiteBasePairs (X.image proj) →
        r ∈ TwoBiteBasePairs (Y.image proj) →
        ((proj a.1 = q.1 ∧ proj a.2 = q.2) ∨
          (proj a.1 = q.2 ∧ proj a.2 = q.1)) →
        ((proj a.1 = r.1 ∧ proj a.2 = r.2) ∨
          (proj a.1 = r.2 ∧ proj a.2 = r.1)) →
        q = r := by
    intro proj X Y a q r hq hr hqproj hrproj
    have hq' := hq
    have hr' := hr
    simp [TwoBiteBasePairs, TwoBitePairsInSet] at hq' hr'
    rcases hq' with ⟨_, hqrank⟩
    rcases hr' with ⟨_, hrrank⟩
    rcases hqproj with hqproj | hqproj <;> rcases hrproj with hrproj | hrproj
    · exact Prod.ext (hqproj.1.symm.trans hrproj.1) (hqproj.2.symm.trans hrproj.2)
    · exfalso
      have hx_lt_y : proj a.1 < proj a.2 := by
        simpa [hqproj.1, hqproj.2] using hqrank
      have hy_lt_x : proj a.2 < proj a.1 := by
        simpa [hrproj.1, hrproj.2] using hrrank
      exact (lt_asymm hx_lt_y) hy_lt_x
    · exfalso
      have hy_lt_x : proj a.2 < proj a.1 := by
        simpa [hqproj.1, hqproj.2] using hqrank
      have hx_lt_y : proj a.1 < proj a.2 := by
        simpa [hrproj.1, hrproj.2] using hrrank
      exact (lt_asymm hx_lt_y) hy_lt_x
    · exact Prod.ext (hqproj.2.symm.trans hrproj.2) (hqproj.1.symm.trans hrproj.1)
  have hRed_same_final_unique :
      ∀ (a : Fin n × Fin n) (q r : Fin m × Fin m),
        Sum.inl q ∈ Q →
        Sum.inl r ∈ Q →
        ((TwoBiteRedProjection ω a.1 = q.1 ∧
            TwoBiteRedProjection ω a.2 = q.2) ∨
          (TwoBiteRedProjection ω a.1 = q.2 ∧
            TwoBiteRedProjection ω a.2 = q.1)) →
        ((TwoBiteRedProjection ω a.1 = r.1 ∧
            TwoBiteRedProjection ω a.2 = r.2) ∨
          (TwoBiteRedProjection ω a.1 = r.2 ∧
            TwoBiteRedProjection ω a.2 = r.1)) →
        q = r := by
    intro a q r hq hr hqproj hrproj
    rcases hQ_mem_cases (Sum.inl q) hq with ⟨xq, _hxqA, hqbase⟩
    rcases hQ_mem_cases (Sum.inl r) hr with ⟨xr, _hxrA, hrbase⟩
    exact hProjectedPair_unique_for_final_pair (TwoBiteRedProjection ω)
      (TwoBiteX ω I xq) (TwoBiteX ω I xr) a q r hqbase hrbase hqproj hrproj
  have hBlue_same_final_unique :
      ∀ (a : Fin n × Fin n) (q r : Fin m × Fin m),
        Sum.inr q ∈ Q →
        Sum.inr r ∈ Q →
        ((TwoBiteBlueProjection ω a.1 = q.1 ∧
            TwoBiteBlueProjection ω a.2 = q.2) ∨
          (TwoBiteBlueProjection ω a.1 = q.2 ∧
            TwoBiteBlueProjection ω a.2 = q.1)) →
        ((TwoBiteBlueProjection ω a.1 = r.1 ∧
            TwoBiteBlueProjection ω a.2 = r.2) ∨
          (TwoBiteBlueProjection ω a.1 = r.2 ∧
            TwoBiteBlueProjection ω a.2 = r.1)) →
        q = r := by
    intro a q r hq hr hqproj hrproj
    rcases hQ_mem_cases (Sum.inr q) hq with ⟨xq, _hxqA, hqbase⟩
    rcases hQ_mem_cases (Sum.inr r) hr with ⟨xr, _hxrA, hrbase⟩
    exact hProjectedPair_unique_for_final_pair (TwoBiteBlueProjection ω)
      (TwoBiteX ω I xq) (TwoBiteX ω I xr) a q r hqbase hrbase hqproj hrproj
  let phi : {e // e ∈ Q} → ({a // a ∈ Fcls} × Bool) := fun e =>
    let a := Classical.choose (hQ_has_final_witness e.1 e.2)
    let ha := Classical.choose_spec (hQ_has_final_witness e.1 e.2)
    (⟨a, ha.1⟩,
      match e.1 with
      | Sum.inl _ => false
      | Sum.inr _ => true)
  have hphi_injective : Function.Injective phi := by
    intro e₁ e₂ hphi
    cases e₁ with
    | mk e₁ he₁ =>
        cases e₂ with
        | mk e₂ he₂ =>
            cases e₁ with
            | inl q =>
                cases e₂ with
                | inl r =>
                    dsimp [phi] at hphi
                    have hfinal_eq :
                        Classical.choose (hQ_has_final_witness (Sum.inl q) he₁) =
                          Classical.choose (hQ_has_final_witness (Sum.inl r) he₂) := by
                      exact congrArg Subtype.val (congrArg Prod.fst hphi)
                    have hqspec :=
                      Classical.choose_spec (hQ_has_final_witness (Sum.inl q) he₁)
                    have hrspec :=
                      Classical.choose_spec (hQ_has_final_witness (Sum.inl r) he₂)
                    have hqr : q = r := by
                      exact hRed_same_final_unique
                        (Classical.choose (hQ_has_final_witness (Sum.inl q) he₁))
                        q r he₁ he₂ hqspec.2 (by simpa [hfinal_eq] using hrspec.2)
                    apply Subtype.ext
                    simp [hqr]
                | inr r =>
                    dsimp [phi] at hphi
                    have htag : false = true := congrArg Prod.snd hphi
                    cases htag
            | inr q =>
                cases e₂ with
                | inl r =>
                    dsimp [phi] at hphi
                    have htag : true = false := congrArg Prod.snd hphi
                    cases htag
                | inr r =>
                    dsimp [phi] at hphi
                    have hfinal_eq :
                        Classical.choose (hQ_has_final_witness (Sum.inr q) he₁) =
                          Classical.choose (hQ_has_final_witness (Sum.inr r) he₂) := by
                      exact congrArg Subtype.val (congrArg Prod.fst hphi)
                    have hqspec :=
                      Classical.choose_spec (hQ_has_final_witness (Sum.inr q) he₁)
                    have hrspec :=
                      Classical.choose_spec (hQ_has_final_witness (Sum.inr r) he₂)
                    have hqr : q = r := by
                      exact hBlue_same_final_unique
                        (Classical.choose (hQ_has_final_witness (Sum.inr q) he₁))
                        q r he₁ he₂ hqspec.2 (by simpa [hfinal_eq] using hrspec.2)
                    apply Subtype.ext
                    simp [hqr]
  have hcard_nat : Q.card ≤ 2 * Fcls.card := by
    have hcard := Fintype.card_le_of_injective phi hphi_injective
    simpa [Fintype.card_coe, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard
  have hcard_real : (Q.card : ℝ) ≤ 2 * (Fcls.card : ℝ) := by
    exact_mod_cast hcard_nat
  simpa [Q, Fcls] using hcard_real
