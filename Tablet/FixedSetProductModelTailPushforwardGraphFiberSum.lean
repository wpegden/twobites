import Tablet.TwoBiteSample
import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEmbedding
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight
import Tablet.GnpGraphWeightSumOne
import Tablet.TwoBiteEventProbabilityInjectionOnly
import Tablet.FixedEmbeddingGraphEventProbability

-- [TABLET NODE: FixedSetProductModelTailPushforwardGraphFiberSum]

open scoped Classical BigOperators

set_option maxHeartbeats 1000000 in
theorem FixedSetProductModelTailPushforwardGraphFiberSum {n : ℕ} (I : Finset (Fin n))
    {m_sub : ℕ} (p_sub : ℝ) (hp0 : 0 ≤ p_sub) (hp1 : p_sub ≤ 1)
    (π : Fin n ↪ (Fin m_sub × Fin m_sub))
    (H : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) → Prop) :
    let P_R := I.image (fun u => (π u).1)
    let P_B := I.image (fun u => (π u).2)
    let D_ω : TwoBiteSample n m_sub p_sub → ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) := fun ω =>
      (fun x => if x ∈ P_R then ∅ else P_R.filter (fun r => ω.1.Adj x r),
       fun y => if y ∈ P_B then ∅ else P_B.filter (fun b => ω.2.1.Adj y b))
    let valid_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : Prop :=
      (∀ x ∈ P_R, D.1 x = ∅) ∧ (∀ x ∉ P_R, D.1 x ⊆ P_R) ∧
      (∀ y ∈ P_B, D.2 y = ∅) ∧ (∀ y ∉ P_B, D.2 y ⊆ P_B)
    let ν_D (D : ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub)))) : ℝ :=
      (∏ x ∈ Finset.univ \ P_R, p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card)) *
      (∏ y ∈ Finset.univ \ P_B, p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card))
    TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π ∧ H (D_ω ω))
    = TwoBiteEventProbability n m_sub p_sub (fun ω => TwoBiteEmbedding ω = π) *
      (Finset.univ.filter (fun D => valid_D D ∧ H D)).sum ν_D := by
-- BODY
  intro P_R P_B D_ω valid_D ν_D
  let cell := fun ω : TwoBiteSample n m_sub p_sub => TwoBiteEmbedding ω = π
  have h_cell_prob : TwoBiteEventProbability n m_sub p_sub cell = UniformInjectionWeight n m_sub := by
    classical
    let C := Fin n ↪ (Fin m_sub × Fin m_sub)
    have h :=
      TwoBiteEventProbabilityInjectionOnly
        (n := n) (m := m_sub) (p := p_sub)
        (event := fun π' : C => π' = π)
    have hfilter :
        @Finset.filter C (fun π' : C => π' = π)
          (fun π' : C => Classical.propDecidable (π' = π)) Finset.univ =
            ({π} : Finset C) := by
      ext π'
      simp
    rw [hfilter] at h
    simpa [cell, TwoBiteEmbedding, C] using h
  have h_Dω_valid : ∀ ω : TwoBiteSample n m_sub p_sub, valid_D (D_ω ω) := by
    intro ω
    dsimp [valid_D, D_ω]
    constructor
    · intro x hx
      simp [hx]
    constructor
    · intro x hx z hz
      have hz' : z ∈ P_R.filter (fun r => ω.1.Adj x r) := by
        simpa [hx] using hz
      exact (Finset.mem_filter.mp hz').1
    constructor
    · intro y hy
      simp [hy]
    · intro y hy z hz
      have hz' : z ∈ P_B.filter (fun b => ω.2.1.Adj y b) := by
        simpa [hy] using hz
      exact (Finset.mem_filter.mp hz').1
  have h_restrict_to_valid :
      TwoBiteEventProbability n m_sub p_sub
          (fun ω => TwoBiteEmbedding ω = π ∧ H (D_ω ω)) =
        TwoBiteEventProbability n m_sub p_sub
          (fun ω => TwoBiteEmbedding ω = π ∧ valid_D (D_ω ω) ∧ H (D_ω ω)) := by
    unfold TwoBiteEventProbability
    congr 1
    ext ω
    simp [h_Dω_valid ω]
  rw [h_restrict_to_valid]
  let graphData :
      SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) →
        ((Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))) :=
    fun G => D_ω (G.1, G.2, π)
  let graphWeight : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) → ℝ :=
    fun G => GnpGraphWeight p_sub G.1 * GnpGraphWeight p_sub G.2
  have h_graph_split :
      TwoBiteEventProbability n m_sub p_sub
          (fun ω => TwoBiteEmbedding ω = π ∧ valid_D (D_ω ω) ∧ H (D_ω ω)) =
        UniformInjectionWeight n m_sub *
          Finset.univ.sum
            (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
              if valid_D (graphData G) ∧ H (graphData G) then graphWeight G else 0) := by
    have h :=
      FixedEmbeddingGraphEventProbability
        (n := n) (m := m_sub) p_sub π
        (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
          valid_D (graphData G) ∧ H (graphData G))
    simpa [graphData, graphWeight, D_ω, TwoBiteEmbedding] using h
  change
    TwoBiteEventProbability n m_sub p_sub
        (fun ω => TwoBiteEmbedding ω = π ∧ valid_D (D_ω ω) ∧ H (D_ω ω)) =
      TwoBiteEventProbability n m_sub p_sub cell *
        (Finset.univ.filter (fun D => valid_D D ∧ H D)).sum ν_D
  rw [h_graph_split, h_cell_prob]
  have h_graphData_valid :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub), valid_D (graphData G) := by
    intro G
    simpa [graphData] using
      h_Dω_valid ((G.1, G.2, π) : TwoBiteSample n m_sub p_sub)
  have h_drop_valid :
      Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if valid_D (graphData G) ∧ H (graphData G) then graphWeight G else 0) =
        Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if H (graphData G) then graphWeight G else 0) := by
    apply Finset.sum_congr rfl
    intro G hG
    by_cases hH : H (graphData G)
    · simp [h_graphData_valid G, hH]
    · simp [hH]
  let Data :=
    (Fin m_sub → Finset (Fin m_sub)) × (Fin m_sub → Finset (Fin m_sub))
  have h_fiber_term :
      ∀ D : Data,
        (Finset.univ.filter
            (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
              graphData G = D)).sum
            (fun G => if H (graphData G) then graphWeight G else 0) =
          if valid_D D ∧ H D then
            (Finset.univ.filter
              (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
                graphData G = D)).sum graphWeight
          else 0 := by
    intro D
    by_cases hvalid : valid_D D
    · by_cases hH : H D
      · rw [if_pos ⟨hvalid, hH⟩]
        apply Finset.sum_congr rfl
        intro G hG
        have hGD : graphData G = D := (Finset.mem_filter.mp hG).2
        simp [hGD, hH]
      · rw [if_neg (by intro h; exact hH h.2)]
        apply Finset.sum_eq_zero
        intro G hG
        have hGD : graphData G = D := (Finset.mem_filter.mp hG).2
        simp [hGD, hH]
    · rw [if_neg (by intro h; exact hvalid h.1)]
      apply Finset.sum_eq_zero
      intro G hG
      have hGD : graphData G = D := (Finset.mem_filter.mp hG).2
      exact False.elim (hvalid (by simpa [hGD] using h_graphData_valid G))
  have h_partition :
      Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if H (graphData G) then graphWeight G else 0) =
        Finset.univ.sum
          (fun D : Data =>
            if valid_D D ∧ H D then
              (Finset.univ.filter
                (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
                  graphData G = D)).sum graphWeight
            else 0) := by
    have h_fiber :=
      Finset.sum_fiberwise
        (s := (Finset.univ : Finset (SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub))))
        (g := graphData)
        (f := fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
          if H (graphData G) then graphWeight G else 0)
    calc
      Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if H (graphData G) then graphWeight G else 0)
          =
          Finset.univ.sum
            (fun D : Data =>
              (Finset.univ.filter
                (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
                  graphData G = D)).sum
                (fun G => if H (graphData G) then graphWeight G else 0)) := by
            simpa [Data] using h_fiber.symm
      _ = Finset.univ.sum
          (fun D : Data =>
            if valid_D D ∧ H D then
              (Finset.univ.filter
                (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
                  graphData G = D)).sum graphWeight
            else 0) := by
            apply Finset.sum_congr rfl
            intro D hD
            exact h_fiber_term D
  rw [h_drop_valid, h_partition]
  rw [Finset.sum_filter]
  let fiberMass : Data → ℝ := fun D =>
    (Finset.univ.filter
      (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
        graphData G = D)).sum graphWeight
  change
    UniformInjectionWeight n m_sub *
        Finset.univ.sum
          (fun D : Data => if valid_D D ∧ H D then fiberMass D else 0) =
      UniformInjectionWeight n m_sub *
        Finset.univ.sum
          (fun D : Data => if valid_D D ∧ H D then ν_D D else 0)
  have h_fiber_mass_suffices :
      (∀ D : Data, valid_D D → fiberMass D = ν_D D) →
        UniformInjectionWeight n m_sub *
            Finset.univ.sum
              (fun D : Data => if valid_D D ∧ H D then fiberMass D else 0) =
          UniformInjectionWeight n m_sub *
            Finset.univ.sum
              (fun D : Data => if valid_D D ∧ H D then ν_D D else 0) := by
    intro hmass
    congr 1
    apply Finset.sum_congr rfl
    intro D hD
    by_cases hVH : valid_D D ∧ H D
    · rw [if_pos hVH, if_pos hVH, hmass D hVH.1]
    · rw [if_neg hVH, if_neg hVH]
  apply h_fiber_mass_suffices
  intro D hDvalid
  have hD_card_le_R :
      ∀ x : Fin m_sub, x ∉ P_R → (D.1 x).card ≤ P_R.card := by
    intro x hx
    exact Finset.card_le_card (hDvalid.2.1 x hx)
  have hD_card_le_B :
      ∀ y : Fin m_sub, y ∉ P_B → (D.2 y).card ≤ P_B.card := by
    intro y hy
    exact Finset.card_le_card (hDvalid.2.2.2 y hy)
  have h_fiber_red_data :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub),
        graphData G = D →
          ∀ x : Fin m_sub, x ∉ P_R →
            D.1 x = P_R.filter (fun r => G.1.Adj x r) := by
    intro G hGD x hx
    have hx_eq := congrArg (fun E => E.1 x) hGD
    simpa [graphData, D_ω, hx] using hx_eq.symm
  have h_fiber_blue_data :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub),
        graphData G = D →
          ∀ y : Fin m_sub, y ∉ P_B →
            D.2 y = P_B.filter (fun b => G.2.Adj y b) := by
    intro G hGD y hy
    have hy_eq := congrArg (fun E => E.2 y) hGD
    simpa [graphData, D_ω, hy] using hy_eq.symm
  have h_fiber_red_adj :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub),
        graphData G = D →
          ∀ x : Fin m_sub, x ∉ P_R →
            ∀ r : Fin m_sub, r ∈ P_R → (r ∈ D.1 x ↔ G.1.Adj x r) := by
    intro G hGD x hx r hr
    rw [h_fiber_red_data G hGD x hx]
    simp [hr]
  have h_fiber_blue_adj :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub),
        graphData G = D →
          ∀ y : Fin m_sub, y ∉ P_B →
            ∀ b : Fin m_sub, b ∈ P_B → (b ∈ D.2 y ↔ G.2.Adj y b) := by
    intro G hGD y hy b hb
    rw [h_fiber_blue_data G hGD y hy]
    simp [hb]
  let redEvent : SimpleGraph (Fin m_sub) → Prop :=
    fun G_R => ∀ x : Fin m_sub, x ∉ P_R →
      D.1 x = P_R.filter (fun r => G_R.Adj x r)
  let blueEvent : SimpleGraph (Fin m_sub) → Prop :=
    fun G_B => ∀ y : Fin m_sub, y ∉ P_B →
      D.2 y = P_B.filter (fun b => G_B.Adj y b)
  have h_graphData_eq_iff :
      ∀ G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub),
        graphData G = D ↔ redEvent G.1 ∧ blueEvent G.2 := by
    intro G
    constructor
    · intro hGD
      constructor
      · intro x hx
        exact h_fiber_red_data G hGD x hx
      · intro y hy
        exact h_fiber_blue_data G hGD y hy
    · intro hRB
      apply Prod.ext
      · funext x
        by_cases hx : x ∈ P_R
        · simp [graphData, D_ω, hx, hDvalid.1 x hx]
        · simpa [graphData, D_ω, hx] using (hRB.1 x hx).symm
      · funext y
        by_cases hy : y ∈ P_B
        · simp [graphData, D_ω, hy, hDvalid.2.2.1 y hy]
        · simpa [graphData, D_ω, hy] using (hRB.2 y hy).symm
  have h_fiberMass_if :
      fiberMass D =
        Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if redEvent G.1 ∧ blueEvent G.2 then graphWeight G else 0) := by
    dsimp [fiberMass]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro G hG
    by_cases hGD : graphData G = D
    · have hRB := (h_graphData_eq_iff G).mp hGD
      rw [if_pos hGD, if_pos hRB]
    · have hRB : ¬ (redEvent G.1 ∧ blueEvent G.2) := by
        intro h
        exact hGD ((h_graphData_eq_iff G).mpr h)
      rw [if_neg hGD, if_neg hRB]
  have h_pair_factor :
      Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if redEvent G.1 ∧ blueEvent G.2 then graphWeight G else 0) =
        (Finset.univ.sum
          (fun G_R : SimpleGraph (Fin m_sub) =>
            if redEvent G_R then GnpGraphWeight p_sub G_R else 0)) *
        (Finset.univ.sum
          (fun G_B : SimpleGraph (Fin m_sub) =>
            if blueEvent G_B then GnpGraphWeight p_sub G_B else 0)) := by
    let blueMass : ℝ :=
      Finset.univ.sum
        (fun G_B : SimpleGraph (Fin m_sub) =>
          if blueEvent G_B then GnpGraphWeight p_sub G_B else 0)
    have hinner :
        ∀ G_R : SimpleGraph (Fin m_sub),
          Finset.univ.sum
              (fun G_B : SimpleGraph (Fin m_sub) =>
                if redEvent G_R ∧ blueEvent G_B then
                  GnpGraphWeight p_sub G_R * GnpGraphWeight p_sub G_B
                else
                  0) =
            (if redEvent G_R then GnpGraphWeight p_sub G_R else 0) * blueMass := by
      intro G_R
      by_cases hR : redEvent G_R
      · rw [if_pos hR]
        calc
          Finset.univ.sum
              (fun G_B : SimpleGraph (Fin m_sub) =>
                if redEvent G_R ∧ blueEvent G_B then
                  GnpGraphWeight p_sub G_R * GnpGraphWeight p_sub G_B
                else
                  0)
              =
              Finset.univ.sum
                (fun G_B : SimpleGraph (Fin m_sub) =>
                  GnpGraphWeight p_sub G_R *
                    (if blueEvent G_B then GnpGraphWeight p_sub G_B else 0)) := by
                apply Finset.sum_congr rfl
                intro G_B hGB
                by_cases hB : blueEvent G_B
                · rw [if_pos ⟨hR, hB⟩, if_pos hB]
                · have hnot : ¬ (redEvent G_R ∧ blueEvent G_B) := by
                    intro h
                    exact hB h.2
                  rw [if_neg hnot, if_neg hB, mul_zero]
          _ =
              GnpGraphWeight p_sub G_R * blueMass := by
                rw [Finset.mul_sum]
      · rw [if_neg hR, zero_mul]
        apply Finset.sum_eq_zero
        intro G_B hGB
        have hnot : ¬ (redEvent G_R ∧ blueEvent G_B) := by
          intro h
          exact hR h.1
        rw [if_neg hnot]
    calc
      Finset.univ.sum
          (fun G : SimpleGraph (Fin m_sub) × SimpleGraph (Fin m_sub) =>
            if redEvent G.1 ∧ blueEvent G.2 then graphWeight G else 0)
          =
          Finset.univ.sum
            (fun G_R : SimpleGraph (Fin m_sub) =>
              Finset.univ.sum
                (fun G_B : SimpleGraph (Fin m_sub) =>
                  if redEvent G_R ∧ blueEvent G_B then
                    GnpGraphWeight p_sub G_R * GnpGraphWeight p_sub G_B
                  else
                    0)) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          Finset.univ.sum
            (fun G_R : SimpleGraph (Fin m_sub) =>
              (if redEvent G_R then GnpGraphWeight p_sub G_R else 0) * blueMass) := by
            apply Finset.sum_congr rfl
            intro G_R hGR
            exact hinner G_R
      _ =
          (Finset.univ.sum
            (fun G_R : SimpleGraph (Fin m_sub) =>
              if redEvent G_R then GnpGraphWeight p_sub G_R else 0)) *
            blueMass := by
            rw [Finset.sum_mul]
      _ =
          (Finset.univ.sum
            (fun G_R : SimpleGraph (Fin m_sub) =>
              if redEvent G_R then GnpGraphWeight p_sub G_R else 0)) *
          (Finset.univ.sum
            (fun G_B : SimpleGraph (Fin m_sub) =>
              if blueEvent G_B then GnpGraphWeight p_sub G_B else 0)) := by
            rfl
  have hIncidentFiber :
      ∀ (P : Finset (Fin m_sub)) (A : Fin m_sub → Finset (Fin m_sub)),
        (∀ x : Fin m_sub, x ∉ P → A x ⊆ P) →
          Finset.univ.sum
              (fun G : SimpleGraph (Fin m_sub) =>
                if (∀ x : Fin m_sub, x ∉ P → A x = P.filter (fun r => G.Adj x r)) then
                  GnpGraphWeight p_sub G
                else
                  0) =
            ∏ x ∈ (Finset.univ : Finset (Fin m_sub)) \ P,
              p_sub ^ (A x).card * (1 - p_sub) ^ (P.card - (A x).card) := by
    intro P A hA
    classical
    have hEdgeCylinder :
        ∀ (fixed : Finset {e : Fin m_sub × Fin m_sub // e.1.val < e.2.val})
          (target : {e : Fin m_sub × Fin m_sub // e.1.val < e.2.val} → Bool),
          Finset.univ.sum
              (fun G : SimpleGraph (Fin m_sub) =>
                if (∀ e, e ∈ fixed → decide (G.Adj e.1.1 e.1.2) = target e) then
                  GnpGraphWeight p_sub G
                else
                  0) =
            fixed.prod (fun e => if target e then p_sub else (1 : ℝ) - p_sub) := by
      intro fixed target
      classical
      have hBoolCylinderProductMass :
          ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
            (p : ℝ) (fixed : Finset ι) (target : ι → Bool),
            Finset.univ.sum
                (fun f : ι → Bool =>
                  if (∀ i, i ∈ fixed → f i = target i) then
                    Finset.univ.prod (fun i : ι => if f i then p else (1 : ℝ) - p)
                  else
                    0) =
              fixed.prod (fun i => if target i then p else (1 : ℝ) - p) := by
        intro ι _ _ p fixed target
        classical
        let w : Bool → ℝ := fun b => if b then p else (1 : ℝ) - p
        let coord : ι → Bool → ℝ :=
          fun i b => if i ∈ fixed then if b = target i then w b else 0 else w b
        have hpoint :
            ∀ f : ι → Bool,
              (if (∀ i, i ∈ fixed → f i = target i) then
                  Finset.univ.prod (fun i : ι => if f i then p else (1 : ℝ) - p)
                else
                  0) =
                Finset.univ.prod (fun i : ι => coord i (f i)) := by
          intro f
          by_cases hfix : ∀ i, i ∈ fixed → f i = target i
          · rw [if_pos hfix]
            apply Finset.prod_congr rfl
            intro i hi
            by_cases hif : i ∈ fixed
            · simp [coord, w, hif, hfix i hif]
            · simp [coord, w, hif]
          · rw [if_neg hfix]
            have hzero : ∃ i, i ∈ fixed ∧ f i ≠ target i := by
              push Not at hfix
              exact hfix
            rcases hzero with ⟨i, hif, hne⟩
            have hmem : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
            rw [Finset.prod_eq_zero hmem]
            simp [coord, hif, hne]
        calc
          Finset.univ.sum
              (fun f : ι → Bool =>
                if (∀ i, i ∈ fixed → f i = target i) then
                  Finset.univ.prod (fun i : ι => if f i then p else (1 : ℝ) - p)
                else
                  0)
              = Finset.univ.sum (fun f : ι → Bool =>
                  Finset.univ.prod (fun i : ι => coord i (f i))) := by
                apply Finset.sum_congr rfl
                intro f hf
                exact hpoint f
          _ = ∑ f ∈ Fintype.piFinset (fun _ : ι => (Finset.univ : Finset Bool)),
                ∏ i : ι, coord i (f i) := by
                rw [Fintype.piFinset_univ]
          _ = ∏ i : ι, ∑ b ∈ (Finset.univ : Finset Bool), coord i b := by
                simpa using
                  (Finset.sum_prod_piFinset
                    (s := (Finset.univ : Finset Bool))
                    (g := fun i : ι => fun b : Bool => coord i b))
          _ = ∏ i : ι, if i ∈ fixed then w (target i) else 1 := by
                apply Finset.prod_congr rfl
                intro i hi
                by_cases hif : i ∈ fixed
                · cases htarget : target i <;> simp [coord, w, hif, htarget]
                · simp [coord, w, hif]
          _ = fixed.prod (fun i => if target i then p else (1 : ℝ) - p) := by
                rw [← Finset.prod_filter]
                have hfilter :
                    (Finset.univ.filter (fun i : ι => i ∈ fixed)) = fixed := by
                  ext i
                  simp
                rw [hfilter]
      let OrientedEdge := {e : Fin m_sub × Fin m_sub // e.1.val < e.2.val}
      let graphBoolEquiv :
          SimpleGraph (Fin m_sub) ≃ (OrientedEdge → Bool) := by
        refine
          { toFun := fun G e => decide (G.Adj e.1.1 e.1.2)
            invFun := fun f =>
              SimpleGraph.mk
                (fun i j =>
                  if h : i.val < j.val then
                    f ⟨(i, j), h⟩ = true
                  else if h' : j.val < i.val then
                    f ⟨(j, i), h'⟩ = true
                  else
                    False)
                (by
                  intro i j
                  by_cases hij : i.val < j.val
                  · have hji : ¬ j.val < i.val := by omega
                    simp [hij, hji]
                  · by_cases hji : j.val < i.val
                    · simp [hij, hji]
                    · simp [hij, hji])
                ⟨fun i => by simp⟩
            left_inv := ?_
            right_inv := ?_ }
        · intro G
          apply SimpleGraph.ext
          funext i j
          apply propext
          by_cases hij : i.val < j.val
          · simp [hij]
          · by_cases hji : j.val < i.val
            · simp [hij, hji, SimpleGraph.adj_comm]
            · have hij_eq : i = j := by
                apply Fin.ext
                omega
              subst j
              simp
        · intro f
          funext e
          rcases e with ⟨⟨i, j⟩, hij⟩
          dsimp
          simp [hij]
      have hweight_eq :
          ∀ G : SimpleGraph (Fin m_sub),
            GnpGraphWeight p_sub G =
              Finset.univ.prod
                (fun e : OrientedEdge =>
                  if graphBoolEquiv G e then p_sub else (1 : ℝ) - p_sub) := by
        intro G
        unfold GnpGraphWeight
        let pred : Fin m_sub × Fin m_sub → Prop := fun x => x.1.val < x.2.val
        let f : Fin m_sub × Fin m_sub → ℝ :=
          fun x => if G.Adj x.1 x.2 then p_sub else (1 : ℝ) - p_sub
        have hprod :
            ((Finset.univ.filter pred).prod f) =
              Finset.univ.prod (fun x : OrientedEdge => f x.1) := by
          simpa [pred, OrientedEdge] using
            (Finset.prod_subtype (s := Finset.univ.filter pred)
              (h := by intro x; simp [pred]) f)
        simpa [graphBoolEquiv, OrientedEdge, pred, f] using hprod
      let cylinderWeight : (OrientedEdge → Bool) → ℝ :=
        fun f =>
          if (∀ e, e ∈ fixed → f e = target e) then
            Finset.univ.prod
              (fun e : OrientedEdge => if f e then p_sub else (1 : ℝ) - p_sub)
          else
            0
      calc
        Finset.univ.sum
            (fun G : SimpleGraph (Fin m_sub) =>
              if (∀ e, e ∈ fixed → decide (G.Adj e.1.1 e.1.2) = target e) then
                GnpGraphWeight p_sub G
              else
                0)
            = Finset.univ.sum
                (fun G : SimpleGraph (Fin m_sub) =>
                  if (∀ e, e ∈ fixed → graphBoolEquiv G e = target e) then
                    Finset.univ.prod
                      (fun e : OrientedEdge =>
                        if graphBoolEquiv G e then p_sub else (1 : ℝ) - p_sub)
                  else
                    0) := by
              apply Finset.sum_congr rfl
              intro G hG
              rw [hweight_eq G]
              rfl
        _ = Finset.univ.sum (fun f : OrientedEdge → Bool => cylinderWeight f) := by
              exact graphBoolEquiv.sum_comp cylinderWeight
        _ = fixed.prod (fun e => if target e then p_sub else (1 : ℝ) - p_sub) := by
              simpa [cylinderWeight] using hBoolCylinderProductMass p_sub fixed target
    let OrientedEdge := {e : Fin m_sub × Fin m_sub // e.1.val < e.2.val}
    let crossing : OrientedEdge → Prop :=
      fun e => (e.1.1 ∉ P ∧ e.1.2 ∈ P) ∨ (e.1.2 ∉ P ∧ e.1.1 ∈ P)
    let fixed : Finset OrientedEdge := Finset.univ.filter crossing
    let target : OrientedEdge → Bool :=
      fun e =>
        if e.1.1 ∈ P then
          decide (e.1.1 ∈ A e.1.2)
        else
          decide (e.1.2 ∈ A e.1.1)
    have hEvent :
        ∀ G : SimpleGraph (Fin m_sub),
          (∀ e, e ∈ fixed → decide (G.Adj e.1.1 e.1.2) = target e) ↔
            (∀ x : Fin m_sub, x ∉ P → A x = P.filter (fun r => G.Adj x r)) := by
      intro G
      constructor
      · intro hfix x hx
        apply Finset.ext
        intro r
        constructor
        · intro hrA
          have hrP : r ∈ P := hA x hx hrA
          have hne : x ≠ r := by
            intro hxr
            exact hx (by simpa [hxr] using hrP)
          by_cases hlt : x.val < r.val
          · let e : OrientedEdge := ⟨(x, r), hlt⟩
            have he_fixed : e ∈ fixed := by
              simp [fixed, crossing, e, hx, hrP]
            have hdec := hfix e he_fixed
            have htarget : target e = true := by
              simp [target, e, hx, hrA]
            have hdec_true : decide (G.Adj x r) = true := by
              simpa [e, htarget] using hdec
            exact Finset.mem_filter.mpr ⟨hrP, of_decide_eq_true hdec_true⟩
          · have hgt : r.val < x.val := by
              have hneq_val : x.val ≠ r.val := by
                intro hv
                exact hne (Fin.ext hv)
              omega
            let e : OrientedEdge := ⟨(r, x), hgt⟩
            have he_fixed : e ∈ fixed := by
              simp [fixed, crossing, e, hx, hrP]
            have hdec := hfix e he_fixed
            have htarget : target e = true := by
              simp [target, e, hrP, hrA]
            have hdec_true : decide (G.Adj r x) = true := by
              simpa [e, htarget] using hdec
            exact Finset.mem_filter.mpr
              ⟨hrP, (SimpleGraph.adj_comm G r x).1 (of_decide_eq_true hdec_true)⟩
        · intro hrFilt
          have hrP : r ∈ P := (Finset.mem_filter.mp hrFilt).1
          have hAdj : G.Adj x r := (Finset.mem_filter.mp hrFilt).2
          have hne : x ≠ r := by
            intro hxr
            exact hx (by simpa [← hxr] using hrP)
          by_cases hlt : x.val < r.val
          · let e : OrientedEdge := ⟨(x, r), hlt⟩
            have he_fixed : e ∈ fixed := by
              simp [fixed, crossing, e, hx, hrP]
            have hdec := hfix e he_fixed
            have hdec_adj : decide (G.Adj x r) = true := by
              exact decide_eq_true hAdj
            have htarget_true : target e = true := by
              simpa [e, hdec_adj] using hdec.symm
            simpa [target, e, hx] using htarget_true
          · have hgt : r.val < x.val := by
              have hneq_val : x.val ≠ r.val := by
                intro hv
                exact hne (Fin.ext hv)
              omega
            let e : OrientedEdge := ⟨(r, x), hgt⟩
            have he_fixed : e ∈ fixed := by
              simp [fixed, crossing, e, hx, hrP]
            have hdec := hfix e he_fixed
            have hAdj_rx : G.Adj r x := (SimpleGraph.adj_comm G x r).1 hAdj
            have hdec_adj : decide (G.Adj r x) = true := by
              exact decide_eq_true hAdj_rx
            have htarget_true : target e = true := by
              simpa [e, hdec_adj] using hdec.symm
            simpa [target, e, hrP] using htarget_true
      · intro hdata e he
        have he_cross : crossing e := (Finset.mem_filter.mp he).2
        rcases he_cross with hleft | hright
        · have hdata_x := hdata e.1.1 hleft.1
          have hiff : e.1.2 ∈ A e.1.1 ↔ G.Adj e.1.1 e.1.2 := by
            constructor
            · intro hmem
              have : e.1.2 ∈ P.filter (fun r => G.Adj e.1.1 r) := by
                simpa [hdata_x] using hmem
              exact (Finset.mem_filter.mp this).2
            · intro hadj
              have : e.1.2 ∈ P.filter (fun r => G.Adj e.1.1 r) :=
                Finset.mem_filter.mpr ⟨hleft.2, hadj⟩
              simpa [hdata_x] using this
          by_cases hmem : e.1.2 ∈ A e.1.1
          · have hadj : G.Adj e.1.1 e.1.2 := hiff.mp hmem
            simp [target, hleft.1, hmem, hadj]
          · have hnotadj : ¬ G.Adj e.1.1 e.1.2 := by
              intro hadj
              exact hmem (hiff.mpr hadj)
            simp [target, hleft.1, hmem, hnotadj]
        · have hdata_x := hdata e.1.2 hright.1
          have hiff : e.1.1 ∈ A e.1.2 ↔ G.Adj e.1.1 e.1.2 := by
            constructor
            · intro hmem
              have : e.1.1 ∈ P.filter (fun r => G.Adj e.1.2 r) := by
                simpa [hdata_x] using hmem
              exact (SimpleGraph.adj_comm G e.1.2 e.1.1).1 (Finset.mem_filter.mp this).2
            · intro hadj
              have : e.1.1 ∈ P.filter (fun r => G.Adj e.1.2 r) :=
                Finset.mem_filter.mpr ⟨hright.2, (SimpleGraph.adj_comm G e.1.1 e.1.2).1 hadj⟩
              simpa [hdata_x] using this
          by_cases hmem : e.1.1 ∈ A e.1.2
          · have hadj : G.Adj e.1.1 e.1.2 := hiff.mp hmem
            simp [target, hright.2, hmem, hadj]
          · have hnotadj : ¬ G.Adj e.1.1 e.1.2 := by
              intro hadj
              exact hmem (hiff.mpr hadj)
            simp [target, hright.2, hmem, hnotadj]
    have hsum_fixed :
        Finset.univ.sum
            (fun G : SimpleGraph (Fin m_sub) =>
              if (∀ x : Fin m_sub, x ∉ P → A x = P.filter (fun r => G.Adj x r)) then
                GnpGraphWeight p_sub G
              else
                0) =
          fixed.prod (fun e => if target e then p_sub else (1 : ℝ) - p_sub) := by
      calc
        Finset.univ.sum
            (fun G : SimpleGraph (Fin m_sub) =>
              if (∀ x : Fin m_sub, x ∉ P → A x = P.filter (fun r => G.Adj x r)) then
                GnpGraphWeight p_sub G
              else
                0)
            =
            Finset.univ.sum
              (fun G : SimpleGraph (Fin m_sub) =>
                if (∀ e, e ∈ fixed → decide (G.Adj e.1.1 e.1.2) = target e) then
                  GnpGraphWeight p_sub G
                else
                  0) := by
              apply Finset.sum_congr rfl
              intro G hG
              by_cases h1 : ∀ e, e ∈ fixed → decide (G.Adj e.1.1 e.1.2) = target e
              · have h2 := (hEvent G).mp h1
                rw [if_pos h2, if_pos h1]
              · have h2 : ¬ (∀ x : Fin m_sub, x ∉ P → A x = P.filter (fun r => G.Adj x r)) := by
                  intro h
                  exact h1 ((hEvent G).mpr h)
                rw [if_neg h2, if_neg h1]
        _ = fixed.prod (fun e => if target e then p_sub else (1 : ℝ) - p_sub) := by
              exact hEdgeCylinder fixed target
    have hfixed_prod :
        fixed.prod (fun e => if target e then p_sub else (1 : ℝ) - p_sub) =
          (((Finset.univ : Finset (Fin m_sub)) \ P).product P).prod
            (fun q => if q.2 ∈ A q.1 then p_sub else (1 : ℝ) - p_sub) := by
      let pairSet := ((Finset.univ : Finset (Fin m_sub)) \ P).product P
      let toPair : OrientedEdge → Fin m_sub × Fin m_sub :=
        fun e => if e.1.1 ∈ P then (e.1.2, e.1.1) else (e.1.1, e.1.2)
      let fromPair : (q : Fin m_sub × Fin m_sub) → q ∈ pairSet → OrientedEdge :=
        fun q hq =>
          if hlt : q.1.val < q.2.val then
            ⟨(q.1, q.2), hlt⟩
          else
            ⟨(q.2, q.1), by
              have hx : q.1 ∉ P := by
                have h := (Finset.mem_product.mp hq).1
                exact (Finset.mem_sdiff.mp h).2
              have hr : q.2 ∈ P := (Finset.mem_product.mp hq).2
              have hne : q.1 ≠ q.2 := by
                intro h
                exact hx (by simpa [← h] using hr)
              have hneq_val : q.1.val ≠ q.2.val := by
                intro hv
                exact hne (Fin.ext hv)
              change q.2.val < q.1.val
              omega⟩
      have h_to_mem : ∀ e (he : e ∈ fixed), toPair e ∈ pairSet := by
        intro e he
        have hec : crossing e := (Finset.mem_filter.mp he).2
        rcases hec with hleft | hright
        · have hnot : e.1.1 ∉ P := hleft.1
          simp [pairSet, toPair, hnot, hleft.2]
        · have hin : e.1.1 ∈ P := hright.2
          simp [pairSet, toPair, hin, hright.1]
      have h_from_mem : ∀ q (hq : q ∈ pairSet), fromPair q hq ∈ fixed := by
        intro q hq
        have hx : q.1 ∉ P := by
          have h := (Finset.mem_product.mp hq).1
          exact (Finset.mem_sdiff.mp h).2
        have hr : q.2 ∈ P := (Finset.mem_product.mp hq).2
        by_cases hlt : q.1.val < q.2.val
        · dsimp [fromPair]
          rw [dif_pos hlt]
          simp [fixed, crossing, hx, hr]
        · dsimp [fromPair]
          rw [dif_neg hlt]
          simp [fixed, crossing, hx, hr]
      have h_right_inv : ∀ q (hq : q ∈ pairSet), toPair (fromPair q hq) = q := by
        intro q hq
        have hx : q.1 ∉ P := by
          have h := (Finset.mem_product.mp hq).1
          exact (Finset.mem_sdiff.mp h).2
        have hr : q.2 ∈ P := (Finset.mem_product.mp hq).2
        by_cases hlt : q.1.val < q.2.val
        · dsimp [fromPair, toPair]
          rw [dif_pos hlt]
          simp [hx]
        · dsimp [fromPair, toPair]
          rw [dif_neg hlt]
          simp [hr]
      have h_to_inj :
          ∀ (e₁ : OrientedEdge) (he₁ : e₁ ∈ fixed)
            (e₂ : OrientedEdge) (he₂ : e₂ ∈ fixed),
            toPair e₁ = toPair e₂ → e₁ = e₂ := by
        intro e₁ he₁ e₂ he₂ hpair
        have hc₁ : crossing e₁ := (Finset.mem_filter.mp he₁).2
        have hc₂ : crossing e₂ := (Finset.mem_filter.mp he₂).2
        rcases e₁ with ⟨⟨a, b⟩, hab⟩
        rcases e₂ with ⟨⟨c, d⟩, hcd⟩
        rcases hc₁ with hleft₁ | hright₁
        · rcases hc₂ with hleft₂ | hright₂
          · have ha : a ∉ P := hleft₁.1
            have hc : c ∉ P := hleft₂.1
            simp [toPair, ha, hc] at hpair
            rcases hpair with ⟨hac, hbd⟩
            subst c
            subst d
            apply Subtype.ext
            rfl
          · have ha : a ∉ P := hleft₁.1
            have hc : c ∈ P := hright₂.2
            simp [toPair, ha, hc] at hpair
            rcases hpair with ⟨had, hbc⟩
            subst d
            subst c
            have hab' : a.val < b.val := by simpa using hab
            have hcd' : b.val < a.val := by simpa using hcd
            omega
        · rcases hc₂ with hleft₂ | hright₂
          · have ha : a ∈ P := hright₁.2
            have hc : c ∉ P := hleft₂.1
            simp [toPair, ha, hc] at hpair
            rcases hpair with ⟨hbc, had⟩
            subst c
            subst d
            have hab' : a.val < b.val := by simpa using hab
            have hcd' : b.val < a.val := by simpa using hcd
            omega
          · have ha : a ∈ P := hright₁.2
            have hc : c ∈ P := hright₂.2
            simp [toPair, ha, hc] at hpair
            rcases hpair with ⟨hbd, hac⟩
            subst d
            subst c
            apply Subtype.ext
            rfl
      have h_to_surj :
          ∀ q ∈ pairSet, ∃ e, ∃ he : e ∈ fixed, toPair e = q := by
        intro q hq
        refine ⟨fromPair q hq, h_from_mem q hq, h_right_inv q hq⟩
      have hfactor : ∀ e (he : e ∈ fixed),
          (if target e then p_sub else (1 : ℝ) - p_sub) =
            (if (toPair e).2 ∈ A (toPair e).1 then p_sub else (1 : ℝ) - p_sub) := by
        intro e he
        have hec : crossing e := (Finset.mem_filter.mp he).2
        rcases hec with hleft | hright
        · have hnot : e.1.1 ∉ P := hleft.1
          simp [target, toPair, hnot]
        · have hin : e.1.1 ∈ P := hright.2
          simp [target, toPair, hin]
      simpa [pairSet] using
        (Finset.prod_bij
          (s := fixed)
          (t := pairSet)
          (f := fun e => if target e then p_sub else (1 : ℝ) - p_sub)
          (g := fun q : Fin m_sub × Fin m_sub => if q.2 ∈ A q.1 then p_sub else (1 : ℝ) - p_sub)
          (fun e _ => toPair e) h_to_mem h_to_inj h_to_surj hfactor)
    have hpair_prod_card :
        (((Finset.univ : Finset (Fin m_sub)) \ P).product P).prod
            (fun q => if q.2 ∈ A q.1 then p_sub else (1 : ℝ) - p_sub) =
          ∏ x ∈ (Finset.univ : Finset (Fin m_sub)) \ P,
            p_sub ^ (A x).card * (1 - p_sub) ^ (P.card - (A x).card) := by
      calc
        (((Finset.univ : Finset (Fin m_sub)) \ P).product P).prod
            (fun q => if q.2 ∈ A q.1 then p_sub else (1 : ℝ) - p_sub)
            =
            ∏ x ∈ (Finset.univ : Finset (Fin m_sub)) \ P,
              ∏ y ∈ P, if y ∈ A x then p_sub else (1 : ℝ) - p_sub := by
              simpa using
                (Finset.prod_product ((Finset.univ : Finset (Fin m_sub)) \ P) P
                  (fun q : Fin m_sub × Fin m_sub =>
                    if q.2 ∈ A q.1 then p_sub else (1 : ℝ) - p_sub))
        _ = ∏ x ∈ (Finset.univ : Finset (Fin m_sub)) \ P,
            p_sub ^ (A x).card * (1 - p_sub) ^ (P.card - (A x).card) := by
            apply Finset.prod_congr rfl
            intro x hx
            have hx_not : x ∉ P := (Finset.mem_sdiff.mp hx).2
            have hsub : A x ⊆ P := hA x hx_not
            have hfilter_eq : P.filter (fun r => r ∈ A x) = A x := by
              apply Finset.ext
              intro r
              constructor
              · intro hr
                exact (Finset.mem_filter.mp hr).2
              · intro hr
                exact Finset.mem_filter.mpr ⟨hsub hr, hr⟩
            have hfilter_not_card :
                (P.filter (fun r => ¬ r ∈ A x)).card = P.card - (A x).card := by
              have hcard :=
                Finset.card_filter_add_card_filter_not (s := P) (p := fun r => r ∈ A x)
              rw [hfilter_eq] at hcard
              omega
            calc
              (∏ y ∈ P, if y ∈ A x then p_sub else (1 : ℝ) - p_sub)
                  =
                  (P.filter (fun y => y ∈ A x)).prod
                      (fun y => if y ∈ A x then p_sub else (1 : ℝ) - p_sub) *
                    (P.filter (fun y => ¬ y ∈ A x)).prod
                      (fun y => if y ∈ A x then p_sub else (1 : ℝ) - p_sub) := by
                    rw [← Finset.prod_filter_mul_prod_filter_not
                      (s := P) (p := fun y => y ∈ A x)
                      (f := fun y => if y ∈ A x then p_sub else (1 : ℝ) - p_sub)]
              _ =
                  (P.filter (fun y => y ∈ A x)).prod (fun _ => p_sub) *
                    (P.filter (fun y => ¬ y ∈ A x)).prod (fun _ => (1 : ℝ) - p_sub) := by
                    congr 1
                    · apply Finset.prod_congr rfl
                      intro y hy
                      exact if_pos (Finset.mem_filter.mp hy).2
                    · apply Finset.prod_congr rfl
                      intro y hy
                      exact if_neg (Finset.mem_filter.mp hy).2
              _ = p_sub ^ (A x).card * (1 - p_sub) ^ (P.card - (A x).card) := by
                    have hprod_pos :
                        (P.filter (fun y => y ∈ A x)).prod (fun _ => p_sub) =
                          p_sub ^ (A x).card := by
                      rw [Finset.prod_const]
                      simp [hfilter_eq]
                    have hprod_neg :
                        (P.filter (fun y => ¬ y ∈ A x)).prod (fun _ => (1 : ℝ) - p_sub) =
                          (1 - p_sub) ^ (P.card - (A x).card) := by
                      rw [Finset.prod_const]
                      simp [hfilter_not_card]
                    rw [hprod_pos, hprod_neg]
    rw [hsum_fixed, hfixed_prod, hpair_prod_card]
  have h_red_mass :
      Finset.univ.sum
          (fun G_R : SimpleGraph (Fin m_sub) =>
            if redEvent G_R then GnpGraphWeight p_sub G_R else 0) =
        ∏ x ∈ Finset.univ \ P_R,
          p_sub ^ (D.1 x).card * (1 - p_sub) ^ (P_R.card - (D.1 x).card) := by
    simpa [redEvent] using
      hIncidentFiber P_R D.1 hDvalid.2.1
  have h_blue_mass :
      Finset.univ.sum
          (fun G_B : SimpleGraph (Fin m_sub) =>
            if blueEvent G_B then GnpGraphWeight p_sub G_B else 0) =
        ∏ y ∈ Finset.univ \ P_B,
          p_sub ^ (D.2 y).card * (1 - p_sub) ^ (P_B.card - (D.2 y).card) := by
    simpa [blueEvent] using
      hIncidentFiber P_B D.2 hDvalid.2.2.2
  rw [h_fiberMass_if, h_pair_factor, h_red_mass, h_blue_mass]
