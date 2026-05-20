import Tablet.FixedSetIndependenceProbability
import Tablet.NaturalIndependenceScaleFitsTarget
import Tablet.NaturalParameterApproximation
import Tablet.IndependenceNumberLess
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteFinalGraph
import Tablet.TwoBiteRegularityEvent
import Tablet.TwoBiteEdgeProbability
import Tablet.TwoBiteIndependenceScale
import Tablet.TwoBiteNaturalIndependenceScale
import Tablet.TwoBiteNaturalReducedVertexCount
import Tablet.NegligibleProbability

-- [TABLET NODE: NoLargeIndependentSetBadRegularProbability]

theorem NoLargeIndependentSetBadRegularProbability :
    ∀ (ε η ε1 ε2 β : ℝ) {n0 : ℕ},
      0 < ε →
      0 < η →
      η < ε →
      β = (1 / 2 : ℝ) →
      ParameterHierarchy η ε1 ε2 n0 →
      (∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ,
          n0 ≤ N ∧
            ∀ {n m : ℕ} {p : ℝ} (I : Finset (Fin n)),
              N < n →
              m = TwoBiteNaturalReducedVertexCount n →
              p = TwoBiteEdgeProbability (1 / 2 : ℝ) n →
              I.card = TwoBiteNaturalIndependenceScale (1 + η) n →
              TwoBiteEventProbability n m p
                  (fun ω =>
                    (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
                      TwoBiteRegularityEvent (k := I.card) η ε1 ε2 ω)
                ≤ δ * ((Nat.choose n I.card : ℝ)⁻¹)) →
      NegligibleProbability
        (fun n =>
          TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n)
            (fun ω =>
              ¬ IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
                ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ∧
              TwoBiteRegularityEvent
                (k := TwoBiteNaturalIndependenceScale (1 + η) n)
                η ε1 ε2 ω)) := by
-- BODY
  intro ε η ε1 ε2 β n0 hε hη hη_lt hβ hHierarchy hFixed
  classical
  have prob_mono :
      ∀ {n m : ℕ} {p : ℝ} {E F : TwoBiteSample n m p → Prop},
        (∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω) →
        (∀ ω, E ω → F ω) →
        TwoBiteEventProbability n m p E ≤
          TwoBiteEventProbability n m p F := by
    intro n m p E F hweight hEF
    unfold TwoBiteEventProbability
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact hEF ω hω)
      (by
        intro ω hωF hωnotE
        exact hweight ω)
  have prob_union_bound :
      ∀ {n m : ℕ} {p : ℝ} {ι : Type}
        (s : Finset ι) (E : ι → TwoBiteSample n m p → Prop),
        (∀ ω : TwoBiteSample n m p, 0 ≤ TwoBiteSampleWeight ω) →
        TwoBiteEventProbability n m p (fun ω => ∃ i ∈ s, E i ω) ≤
          s.sum (fun i => TwoBiteEventProbability n m p (E i)) := by
    intro n m p ι s E hweight
    let Ω := TwoBiteSample n m p
    let w : Ω → ℝ := fun ω => TwoBiteSampleWeight ω
    have hpoint :
        ∀ ω : Ω,
          (if ∃ i ∈ s, E i ω then w ω else 0) ≤
            s.sum (fun i => if E i ω then w ω else 0) := by
      intro ω
      by_cases h : ∃ i ∈ s, E i ω
      · rcases h with ⟨i, hi, hEi⟩
        have hex : ∃ i ∈ s, E i ω := ⟨i, hi, hEi⟩
        have hnonneg :
            ∀ j ∈ s, 0 ≤ (if E j ω then w ω else 0) := by
          intro j hj
          by_cases hEj : E j ω <;> simp [hEj, w, hweight ω]
        have hle :
            w ω ≤ s.sum (fun j => if E j ω then w ω else 0) := by
          simpa [hEi] using Finset.single_le_sum hnonneg hi
        simpa [hex] using hle
      · have hnonneg :
            0 ≤ s.sum (fun i => if E i ω then w ω else 0) := by
          exact Finset.sum_nonneg (by
            intro i hi
            by_cases hEi : E i ω <;> simp [hEi, w, hweight ω])
        simpa [h] using hnonneg
    calc
      TwoBiteEventProbability n m p (fun ω => ∃ i ∈ s, E i ω)
          = ∑ ω : Ω, if ∃ i ∈ s, E i ω then w ω else 0 := by
              unfold TwoBiteEventProbability
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl ?_
              intro ω hω
              by_cases h : ∃ i ∈ s, E i ω <;> simp [h, w]
      _ ≤ ∑ ω : Ω, s.sum (fun i => if E i ω then w ω else 0) := by
              exact Finset.sum_le_sum (by intro ω hω; exact hpoint ω)
      _ = s.sum (fun i => ∑ ω : Ω, if E i ω then w ω else 0) := by
              rw [Finset.sum_comm]
      _ = s.sum (fun i => TwoBiteEventProbability n m p (E i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              unfold TwoBiteEventProbability
              rw [Finset.sum_filter]
  unfold NegligibleProbability
  let prob : ℕ → ℝ := fun n =>
    TwoBiteEventProbability n (TwoBiteNaturalReducedVertexCount n)
      (TwoBiteEdgeProbability β n)
      (fun ω =>
        ¬ IndependenceNumberLess (TwoBiteFinalGraph ω).2.2
          ((1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ∧
        TwoBiteRegularityEvent
          (k := TwoBiteNaturalIndependenceScale (1 + η) n)
          η ε1 ε2 ω)
  have hweights :
      ∀ᶠ n in Filter.atTop,
        ∀ ω : TwoBiteSample n (TwoBiteNaturalReducedVertexCount n)
            (TwoBiteEdgeProbability β n),
          0 ≤ TwoBiteSampleWeight ω := by
    rcases hHierarchy with
      ⟨hε2_pos, hε2_lt, hε1_lt, hη_lt_one, hη_lt_sixteen, hthree,
        height, hn0sq, hEventually⟩
    filter_upwards [Filter.eventually_gt_atTop n0] with n hn
    intro ω
    have hcomp := hEventually n hn
    dsimp only at hcomp
    rcases hcomp with ⟨hm_pos, hp_nonneg, hp_le_half, hrest⟩
    have hp_nonneg' : 0 ≤ TwoBiteEdgeProbability β n := by
      simpa [hβ, TwoBiteEdgeProbability] using hp_nonneg
    have hp_le_one' : TwoBiteEdgeProbability β n ≤ 1 := by
      have hp_le_half' : TwoBiteEdgeProbability β n ≤ (1 / 2 : ℝ) := by
        simpa [hβ, TwoBiteEdgeProbability] using hp_le_half
      linarith
    exact TwoBiteSampleWeightNonnegative ω hp_nonneg' hp_le_one'
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hweights] with n hnw
    have hnonneg : 0 ≤ prob n := by
      unfold prob TwoBiteEventProbability
      exact Finset.sum_nonneg (by
        intro ω hω
        exact hnw ω)
    linarith
  · intro ρ hρ
    let δ : ℝ := ρ / 2
    have hδ : 0 < δ := by
      dsimp [δ]
      linarith
    obtain ⟨Nfixed, hNfixed_ge, hFixedN⟩ := hFixed δ hδ
    obtain ⟨Nfit, hFit⟩ := NaturalIndependenceScaleFitsTarget ε η hη hη_lt
    let N := max Nfixed Nfit
    filter_upwards [Filter.eventually_gt_atTop N, hweights] with n hn hnw
    let M := TwoBiteNaturalReducedVertexCount n
    let pβ := TwoBiteEdgeProbability β n
    let K := TwoBiteNaturalIndependenceScale (1 + η) n
    let target : ℝ := (1 + ε) * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))
    let R : TwoBiteSample n M pβ → Prop :=
      fun ω => TwoBiteRegularityEvent (k := K) η ε1 ε2 ω
    let Bad : TwoBiteSample n M pβ → Prop :=
      fun ω => ¬ IndependenceNumberLess (TwoBiteFinalGraph ω).2.2 target ∧ R ω
    let C : Finset (Finset (Fin n)) :=
      Finset.univ.filter (fun I : Finset (Fin n) => I.card = K)
    let E : Finset (Fin n) → TwoBiteSample n M pβ → Prop :=
      fun I ω =>
        (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) ∧
          TwoBiteRegularityEvent (k := I.card) η ε1 ε2 ω
    have hNfixed_lt : Nfixed < n :=
      lt_of_le_of_lt (Nat.le_max_left Nfixed Nfit) hn
    have hNfit_le : Nfit ≤ n :=
      le_of_lt (lt_of_le_of_lt (Nat.le_max_right Nfixed Nfit) hn)
    have hK_lt_target : (K : ℝ) < target := by
      simpa [K, target, TwoBiteIndependenceScale] using hFit n hNfit_le
    have hsubset : ∀ ω, Bad ω → ∃ I ∈ C, E I ω := by
      intro ω hω
      rcases hω with ⟨hbad, hRω⟩
      unfold IndependenceNumberLess at hbad
      push Not at hbad
      rcases hbad with ⟨J, hJindep, hJcard_ge⟩
      have hK_le_J : K ≤ J.card := by
        exact_mod_cast (le_of_lt (lt_of_lt_of_le hK_lt_target hJcard_ge))
      obtain ⟨I, hIJ, hIcard⟩ := Finset.exists_subset_card_eq hK_le_J
      have hImem : I ∈ C := by
        simp [C, hIcard]
      have hIindep : (TwoBiteFinalGraph ω).2.2.IsIndepSet (↑I : Set (Fin n)) := by
        rw [SimpleGraph.isIndepSet_iff] at hJindep ⊢
        exact hJindep.mono (by
          intro x hx
          exact hIJ hx)
      refine ⟨I, hImem, ?_⟩
      refine ⟨hIindep, ?_⟩
      simpa [E, R, hIcard] using hRω
    have hbad_le_union :
        TwoBiteEventProbability n M pβ Bad ≤
          TwoBiteEventProbability n M pβ (fun ω => ∃ I ∈ C, E I ω) :=
      prob_mono hnw hsubset
    have hunion_bound :
        TwoBiteEventProbability n M pβ (fun ω => ∃ I ∈ C, E I ω) ≤
          C.sum (fun I => TwoBiteEventProbability n M pβ (E I)) :=
      prob_union_bound C E hnw
    have hfixed_each :
        ∀ I ∈ C,
          TwoBiteEventProbability n M pβ (E I) ≤
            δ * ((Nat.choose n K : ℝ)⁻¹) := by
      intro I hIC
      have hIcard : I.card = K := by
        simpa [C] using hIC
      have hp : pβ = TwoBiteEdgeProbability (1 / 2 : ℝ) n := by
        simp [pβ, hβ]
      have hbound :=
        hFixedN (n := n) (m := M) (p := pβ) I hNfixed_lt rfl hp hIcard
      simpa [E, M, pβ, hIcard] using hbound
    have hsum_bound :
        C.sum (fun I => TwoBiteEventProbability n M pβ (E I)) ≤
          C.sum (fun _I => δ * ((Nat.choose n K : ℝ)⁻¹)) := by
      exact Finset.sum_le_sum (by
        intro I hIC
        exact hfixed_each I hIC)
    have hCcard : C.card = Nat.choose n K := by
      simp [C]
    have hsum_eval :
        C.sum (fun _I => δ * ((Nat.choose n K : ℝ)⁻¹)) =
          (Nat.choose n K : ℝ) * (δ * ((Nat.choose n K : ℝ)⁻¹)) := by
      rw [Finset.sum_const, nsmul_eq_mul, hCcard]
    have hcancel :
        (Nat.choose n K : ℝ) * (δ * ((Nat.choose n K : ℝ)⁻¹)) ≤ δ := by
      by_cases hzero : (Nat.choose n K : ℝ) = 0
      · simp [hzero, le_of_lt hδ]
      · calc
          (Nat.choose n K : ℝ) * (δ * ((Nat.choose n K : ℝ)⁻¹))
              = δ * ((Nat.choose n K : ℝ) * ((Nat.choose n K : ℝ)⁻¹)) := by
                ring
          _ = δ := by
                rw [mul_inv_cancel₀ hzero, mul_one]
          _ ≤ δ := le_rfl
    have hprob_le_delta : prob n ≤ δ := by
      calc
        prob n = TwoBiteEventProbability n M pβ Bad := by
          simp [prob, M, pβ, Bad, R, target, K]
        _ ≤ TwoBiteEventProbability n M pβ (fun ω => ∃ I ∈ C, E I ω) :=
          hbad_le_union
        _ ≤ C.sum (fun I => TwoBiteEventProbability n M pβ (E I)) :=
          hunion_bound
        _ ≤ C.sum (fun _I => δ * ((Nat.choose n K : ℝ)⁻¹)) :=
          hsum_bound
        _ = (Nat.choose n K : ℝ) * (δ * ((Nat.choose n K : ℝ)⁻¹)) :=
          hsum_eval
        _ ≤ δ := hcancel
    have hδ_lt : δ < ρ := by
      dsimp [δ]
      linarith
    exact lt_of_le_of_lt hprob_le_delta hδ_lt
