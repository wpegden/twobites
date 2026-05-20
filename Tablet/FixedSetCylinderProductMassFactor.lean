import Tablet.TwoBiteEventProbability
import Tablet.TwoBiteEdgeCoordinateValue
import Tablet.TwoBiteSampleWeight
import Tablet.GnpGraphWeight
import Tablet.UniformInjectionWeight

-- [TABLET NODE: FixedSetCylinderProductMassFactor]

set_option maxHeartbeats 1000000 in
theorem FixedSetCylinderProductMassFactor :
    ∀ {n m : ℕ} {p : ℝ}
      (hist : TwoBiteSample n m p → Prop)
      (recorded product :
        Finset (Sum (Fin m × Fin m) (Fin m × Fin m)))
      (ω0 : TwoBiteSample n m p),
      0 < p →
      p < 1 →
      hist ω0 →
      (∀ ω : TwoBiteSample n m p,
        hist ω ↔
          (∀ x : Fin n, ω.2.2 x = ω0.2.2 x) ∧
          (∀ e,
            e ∈ recorded →
              (TwoBiteEdgeCoordinateValue ω e ↔
                TwoBiteEdgeCoordinateValue ω0 e))) →
      (∀ e, e ∈ recorded →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val) →
      (∀ e, e ∈ product → e ∉ recorded) →
      (∀ e, e ∈ product →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val) →
      ∀ A : Finset (Sum (Fin m × Fin m) (Fin m × Fin m)),
        A ⊆ product →
          TwoBiteEventProbability n m p hist ≠ 0 ∧
          TwoBiteEventProbability n m p
              (fun ω =>
                (∀ e, e ∈ product →
                  (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)) ∧
                hist ω) =
            (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card)) *
              TwoBiteEventProbability n m p hist := by
-- BODY
  intro n m p hist recorded product ω0 hp_pos hp_lt hhist0 hCylinder
    hRecordedOriented hProductUnrecorded hProductOriented A hAproduct
  classical
  have hOneMinusPos : 0 < (1 : ℝ) - p :=
    sub_pos.mpr hp_lt
  have hGnpGraphWeight_pos :
      ∀ G : SimpleGraph (Fin m), 0 < GnpGraphWeight p G := by
    intro G
    unfold GnpGraphWeight
    apply Finset.prod_pos
    intro e he
    by_cases hAdj : G.Adj e.1 e.2
    · simp [hAdj, hp_pos]
    · simp [hAdj, hOneMinusPos]
  have hInjectionCard_pos :
      0 < Fintype.card (Fin n ↪ (Fin m × Fin m)) :=
    Fintype.card_pos_iff.mpr ⟨ω0.2.2⟩
  have hInjectionCard_ne :
      Fintype.card (Fin n ↪ (Fin m × Fin m)) ≠ 0 :=
    Nat.ne_of_gt hInjectionCard_pos
  have hUniformInjectionWeight_pos :
      0 < UniformInjectionWeight n m := by
    unfold UniformInjectionWeight
    rw [if_neg hInjectionCard_ne]
    exact inv_pos.mpr (Nat.cast_pos.mpr hInjectionCard_pos)
  have hSampleWeight_pos :
      ∀ ω : TwoBiteSample n m p, 0 < TwoBiteSampleWeight ω := by
    intro ω
    unfold TwoBiteSampleWeight
    exact mul_pos
      (mul_pos (hGnpGraphWeight_pos ω.1) (hGnpGraphWeight_pos ω.2.1))
      hUniformInjectionWeight_pos
  have hDenominatorMass_pos :
      0 < TwoBiteEventProbability n m p hist := by
    unfold TwoBiteEventProbability
    apply Finset.sum_pos
    · intro ω hω
      exact hSampleWeight_pos ω
    · exact ⟨ω0, by simp [hhist0]⟩
  have hDenominatorNonzero :
      TwoBiteEventProbability n m p hist ≠ 0 :=
    ne_of_gt hDenominatorMass_pos
  let productEvent : TwoBiteSample n m p → Prop :=
    fun ω =>
      ∀ e, e ∈ product →
        (TwoBiteEdgeCoordinateValue ω e ↔ e ∈ A)
  let injectionEvent : TwoBiteSample n m p → Prop :=
    fun ω => ∀ x : Fin n, ω.2.2 x = ω0.2.2 x
  let recordedEvent : TwoBiteSample n m p → Prop :=
    fun ω =>
      ∀ e,
        e ∈ recorded →
          (TwoBiteEdgeCoordinateValue ω e ↔
            TwoBiteEdgeCoordinateValue ω0 e)
  have hHistCylinder :
      ∀ ω : TwoBiteSample n m p,
        hist ω ↔ injectionEvent ω ∧ recordedEvent ω := by
    intro ω
    simpa [injectionEvent, recordedEvent] using hCylinder ω
  have hEventProbability_congr :
      ∀ E F : TwoBiteSample n m p → Prop,
        (∀ ω, E ω ↔ F ω) →
          TwoBiteEventProbability n m p E =
            TwoBiteEventProbability n m p F := by
    intro E F hiff
    unfold TwoBiteEventProbability
    have hfilter :
        (Finset.univ.filter (fun ω : TwoBiteSample n m p => E ω)) =
          (Finset.univ.filter (fun ω : TwoBiteSample n m p => F ω)) := by
      ext ω
      simp [hiff ω]
    rw [hfilter]
  have hDenominatorCylinder :
      TwoBiteEventProbability n m p hist =
        TwoBiteEventProbability n m p
          (fun ω => injectionEvent ω ∧ recordedEvent ω) := by
    exact hEventProbability_congr hist
      (fun ω => injectionEvent ω ∧ recordedEvent ω) hHistCylinder
  have hNumeratorCylinder :
      TwoBiteEventProbability n m p
          (fun ω => productEvent ω ∧ hist ω) =
        TwoBiteEventProbability n m p
          (fun ω =>
            productEvent ω ∧ injectionEvent ω ∧ recordedEvent ω) := by
    apply hEventProbability_congr
    intro ω
    rw [hHistCylinder ω]
  have hEventSplit :
      ∀ ω : TwoBiteSample n m p,
        productEvent ω ↔
          (∀ e, e ∈ A → TwoBiteEdgeCoordinateValue ω e) ∧
          (∀ e, e ∈ product \ A → ¬ TwoBiteEdgeCoordinateValue ω e) := by
    intro ω
    constructor
    · intro hω
      constructor
      · intro e heA
        exact (hω e (hAproduct heA)).2 heA
      · intro e heDiff hedge
        have heProduct : e ∈ product := (Finset.mem_sdiff.mp heDiff).1
        have heNotA : e ∉ A := (Finset.mem_sdiff.mp heDiff).2
        exact heNotA ((hω e heProduct).1 hedge)
    · intro hω e heProduct
      constructor
      · intro hedge
        by_contra heNotA
        exact (hω.2 e (Finset.mem_sdiff.mpr ⟨heProduct, heNotA⟩)) hedge
      · intro heA
        exact hω.1 e heA
  have hAInterProduct : A ∩ product = A := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      exact (Finset.mem_inter.mp he).1
    · intro heA
      exact Finset.mem_inter.mpr ⟨heA, hAproduct heA⟩
  have hProductDiffCard :
      (product \ A).card = product.card - A.card := by
    rw [Finset.card_sdiff, hAInterProduct]
  have hProdDiffFactor :
      (product \ A).prod (fun e =>
        if e ∈ A then p else (1 : ℝ) - p) =
        ((1 : ℝ) - p) ^ (product \ A).card := by
    calc
      (product \ A).prod (fun e =>
          if e ∈ A then p else (1 : ℝ) - p)
          = (product \ A).prod (fun _ => (1 : ℝ) - p) := by
            apply Finset.prod_congr rfl
            intro e he
            simp [(Finset.mem_sdiff.mp he).2]
      _ = ((1 : ℝ) - p) ^ (product \ A).card := by
            simp
  have hProdAFactor :
      A.prod (fun e => if e ∈ A then p else (1 : ℝ) - p) =
        p ^ A.card := by
    calc
      A.prod (fun e => if e ∈ A then p else (1 : ℝ) - p)
          = A.prod (fun _ => p) := by
            apply Finset.prod_congr rfl
            intro e he
            simp [he]
      _ = p ^ A.card := by
            simp
  have hFactorProduct :
      product.prod (fun e =>
        if e ∈ A then p else (1 : ℝ) - p) =
        p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    calc
      product.prod (fun e =>
          if e ∈ A then p else (1 : ℝ) - p)
          =
          (product \ A).prod (fun e =>
              if e ∈ A then p else (1 : ℝ) - p) *
            A.prod (fun e =>
              if e ∈ A then p else (1 : ℝ) - p) := by
            rw [← Finset.prod_sdiff hAproduct]
      _ = ((1 : ℝ) - p) ^ (product \ A).card * p ^ A.card := by
            rw [hProdDiffFactor, hProdAFactor]
      _ = p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
            rw [hProductDiffCard, mul_comm]
  have hProductEventFactor :
      ∀ ω : TwoBiteSample n m p,
        productEvent ω →
          product.prod
              (fun e =>
                if TwoBiteEdgeCoordinateValue ω e then
                  p
                else
                  (1 : ℝ) - p) =
            p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    intro ω hω
    calc
      product.prod
          (fun e =>
            if TwoBiteEdgeCoordinateValue ω e then
              p
            else
              (1 : ℝ) - p)
          =
          product.prod (fun e =>
            if e ∈ A then p else (1 : ℝ) - p) := by
            apply Finset.prod_congr rfl
            intro e heProduct
            by_cases hedge : TwoBiteEdgeCoordinateValue ω e
            · have heA : e ∈ A := (hω e heProduct).1 hedge
              simp [hedge, heA]
            · have heNotA : e ∉ A := by
                intro heA
                exact hedge ((hω e heProduct).2 heA)
              simp [hedge, heNotA]
      _ = p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) :=
            hFactorProduct
  have hAUnrecorded :
      ∀ e, e ∈ A → e ∉ recorded := by
    intro e heA
    exact hProductUnrecorded e (hAproduct heA)
  have hProductDiffUnrecorded :
      ∀ e, e ∈ product \ A → e ∉ recorded := by
    intro e heDiff
    exact hProductUnrecorded e (Finset.mem_sdiff.mp heDiff).1
  have hAOriented :
      ∀ e, e ∈ A →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val := by
    intro e heA
    exact hProductOriented e (hAproduct heA)
  have hProductDiffOriented :
      ∀ e, e ∈ product \ A →
        match e with
        | Sum.inl q => q.1.val < q.2.val
        | Sum.inr q => q.1.val < q.2.val := by
    intro e heDiff
    exact hProductOriented e (Finset.mem_sdiff.mp heDiff).1
  have hProductEventFactorUnfolded :
      ∀ ω : TwoBiteSample n m p,
        productEvent ω →
          product.prod
              (fun e =>
                if
                    match e with
                    | Sum.inl q => ω.1.Adj q.1 q.2
                    | Sum.inr q => ω.2.1.Adj q.1 q.2
                then
                  p
                else
                  (1 : ℝ) - p) =
            p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    intro ω hω
    simpa [TwoBiteEdgeCoordinateValue, TwoBiteRedGraph, TwoBiteBlueGraph]
      using hProductEventFactor ω hω
  have hCylinderFilter :
      (Finset.univ.filter
          (fun ω : TwoBiteSample n m p =>
            injectionEvent ω ∧ recordedEvent ω)) =
        ((Finset.univ.filter
            (fun ω : TwoBiteSample n m p => injectionEvent ω)).filter
          (fun ω => recordedEvent ω)) := by
    ext ω
    simp
  have hProductCylinderFilter :
      (Finset.univ.filter
          (fun ω : TwoBiteSample n m p =>
            productEvent ω ∧ injectionEvent ω ∧ recordedEvent ω)) =
        (((Finset.univ.filter
            (fun ω : TwoBiteSample n m p => injectionEvent ω)).filter
          (fun ω => recordedEvent ω)).filter
          (fun ω => productEvent ω)) := by
    ext ω
    simp [and_assoc, and_comm]
  have hProductCylinderContribution :
      ∀ ω : TwoBiteSample n m p,
        ω ∈
            (((Finset.univ.filter
                (fun ω : TwoBiteSample n m p => injectionEvent ω)).filter
              (fun ω => recordedEvent ω)).filter
              (fun ω => productEvent ω)) →
          product.prod
              (fun e =>
                if
                    match e with
                    | Sum.inl q => ω.1.Adj q.1 q.2
                    | Sum.inr q => ω.2.1.Adj q.1 q.2
                then
                  p
                else
                  (1 : ℝ) - p) =
            p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    intro ω hω
    exact hProductEventFactorUnfolded ω (Finset.mem_filter.mp hω).2
  have hBoolCylinderProductMass :
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (fixed : Finset ι) (target : ι → Bool),
        Finset.univ.sum
            (fun f : ι → Bool =>
              if (∀ i, i ∈ fixed → f i = target i) then
                Finset.univ.prod (fun i : ι =>
                  if f i then p else (1 : ℝ) - p)
              else
                0) =
          fixed.prod (fun i => if target i then p else (1 : ℝ) - p) := by
    intro ι _ _ fixed target
    classical
    let w : Bool → ℝ := fun b => if b then p else (1 : ℝ) - p
    let coord : ι → Bool → ℝ :=
      fun i b =>
        if i ∈ fixed then
          if b = target i then w b else 0
        else
          w b
    have hpoint :
        ∀ f : ι → Bool,
          (if (∀ i, i ∈ fixed → f i = target i) then
              Finset.univ.prod (fun i : ι => w (f i))
            else
              0) =
            Finset.univ.prod (fun i : ι => coord i (f i)) := by
      intro f
      by_cases hf : ∀ i, i ∈ fixed → f i = target i
      · rw [if_pos hf]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hif : i ∈ fixed
        · simp [coord, hif, hf i hif]
        · simp [coord, hif]
      · rw [if_neg hf]
        have hex : ∃ i, i ∈ fixed ∧ f i ≠ target i := by
          push Not at hf
          exact hf
        rcases hex with ⟨i, hif, hneq⟩
        have hzero : coord i (f i) = 0 := by
          dsimp [coord]
          rw [if_pos hif, if_neg hneq]
        exact (Finset.prod_eq_zero (Finset.mem_univ i) hzero).symm
    calc
      Finset.univ.sum
            (fun f : ι → Bool =>
              if (∀ i, i ∈ fixed → f i = target i) then
                Finset.univ.prod (fun i : ι =>
                  if f i then p else (1 : ℝ) - p)
              else
                0)
          = Finset.univ.sum (fun f : ι → Bool =>
              Finset.univ.prod (fun i : ι => coord i (f i))) := by
            apply Finset.sum_congr rfl
            intro f hf
            simpa [w] using hpoint f
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
  let OrientedEdge := {e : Fin m × Fin m // e.1.val < e.2.val}
  let graphBoolEquiv :
      SimpleGraph (Fin m) ≃ (OrientedEdge → Bool) := by
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
  have hGraphWeightBoolProduct :
      ∀ G : SimpleGraph (Fin m),
        GnpGraphWeight p G =
          Finset.univ.prod
            (fun e : OrientedEdge =>
              if graphBoolEquiv G e then p else (1 : ℝ) - p) := by
    intro G
    unfold GnpGraphWeight
    let pred : Fin m × Fin m → Prop := fun x => x.1.val < x.2.val
    let f : Fin m × Fin m → ℝ :=
      fun x => if G.Adj x.1 x.2 then p else (1 : ℝ) - p
    have hprod :
        ((Finset.univ.filter pred).prod f) =
          Finset.univ.prod (fun x : OrientedEdge => f x.1) := by
      simpa [pred, OrientedEdge] using
        (Finset.prod_subtype (s := Finset.univ.filter pred)
          (h := by intro x; simp [pred]) f)
    simpa [graphBoolEquiv, OrientedEdge, pred, f] using hprod
  let GraphCoord := Sum OrientedEdge OrientedEdge
  let graphPairBoolEquiv :
      SimpleGraph (Fin m) × SimpleGraph (Fin m) ≃ (GraphCoord → Bool) := by
    refine
      { toFun := fun x c =>
          match c with
          | Sum.inl e => graphBoolEquiv x.1 e
          | Sum.inr e => graphBoolEquiv x.2 e
        invFun := fun f =>
          (graphBoolEquiv.symm (fun e => f (Sum.inl e)),
            graphBoolEquiv.symm (fun e => f (Sum.inr e)))
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      apply Prod.ext
      · exact graphBoolEquiv.left_inv x.1
      · exact graphBoolEquiv.left_inv x.2
    · intro f
      funext c
      cases c with
      | inl e =>
          exact congrFun (graphBoolEquiv.right_inv (fun e => f (Sum.inl e))) e
      | inr e =>
          exact congrFun (graphBoolEquiv.right_inv (fun e => f (Sum.inr e))) e
  have hPairWeightBoolProduct :
      ∀ x : SimpleGraph (Fin m) × SimpleGraph (Fin m),
        GnpGraphWeight p x.1 * GnpGraphWeight p x.2 =
          Finset.univ.prod
            (fun c : GraphCoord =>
              if graphPairBoolEquiv x c then p else (1 : ℝ) - p) := by
    intro x
    rw [hGraphWeightBoolProduct x.1, hGraphWeightBoolProduct x.2]
    simp [GraphCoord, graphPairBoolEquiv, Fintype.prod_sum_type]
  have hPairCylinderMass :
      ∀ (fixed : Finset GraphCoord) (target : GraphCoord → Bool),
        Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if (∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c) then
                GnpGraphWeight p x.1 * GnpGraphWeight p x.2
              else
                0) =
          fixed.prod (fun c => if target c then p else (1 : ℝ) - p) := by
    intro fixed target
    let pairWeight : (GraphCoord → Bool) → ℝ :=
      fun f =>
        Finset.univ.prod (fun c : GraphCoord =>
          if f c then p else (1 : ℝ) - p)
    let cylinderWeight : (GraphCoord → Bool) → ℝ :=
      fun f =>
        if (∀ c, c ∈ fixed → f c = target c) then
          pairWeight f
        else
          0
    calc
      Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if (∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c) then
                GnpGraphWeight p x.1 * GnpGraphWeight p x.2
              else
                0)
          = Finset.univ.sum
              (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
                cylinderWeight (graphPairBoolEquiv x)) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hfix :
                ∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c
            · rw [if_pos hfix]
              rw [hPairWeightBoolProduct x]
              dsimp [cylinderWeight, pairWeight]
              rw [if_pos hfix]
            · rw [if_neg hfix]
              dsimp [cylinderWeight]
              rw [if_neg hfix]
      _ = Finset.univ.sum (fun f : GraphCoord → Bool => cylinderWeight f) := by
            exact graphPairBoolEquiv.sum_comp cylinderWeight
      _ = fixed.prod (fun c => if target c then p else (1 : ℝ) - p) := by
            simpa [cylinderWeight, pairWeight, GraphCoord] using
              (hBoolCylinderProductMass fixed target)
  have hPairCylinderMassScalar :
      ∀ (fixed : Finset GraphCoord) (target : GraphCoord → Bool) (u : ℝ),
        Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if (∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c) then
                (GnpGraphWeight p x.1 * GnpGraphWeight p x.2) * u
              else
                0) =
          fixed.prod (fun c => if target c then p else (1 : ℝ) - p) * u := by
    intro fixed target u
    calc
      Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if (∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c) then
                (GnpGraphWeight p x.1 * GnpGraphWeight p x.2) * u
              else
                0)
          =
          (Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if (∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c) then
                GnpGraphWeight p x.1 * GnpGraphWeight p x.2
              else
                0)) * u := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hfix :
                ∀ c, c ∈ fixed → graphPairBoolEquiv x c = target c
            · rw [if_pos hfix, if_pos hfix]
            · rw [if_neg hfix, if_neg hfix]
              ring
      _ = fixed.prod (fun c => if target c then p else (1 : ℝ) - p) * u := by
            rw [hPairCylinderMass fixed target]
  have hInjectionFixedSum :
      ∀ {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
        [DecidableEq γ]
        (γ0 : γ) (P : α → β → Prop) [∀ a b, Decidable (P a b)]
        (F : α → β → ℝ) (u : ℝ),
        (Finset.univ.sum
          (fun x : α × (β × γ) =>
            if x.2.2 = γ0 ∧ P x.1 x.2.1 then
              F x.1 x.2.1 * u
            else
              0)) =
          Finset.univ.sum
            (fun a : α =>
              Finset.univ.sum
                (fun b : β =>
                  if P a b then F a b * u else 0)) := by
    intro α β γ _ _ _ _ γ0 P _ F u
    calc
      Finset.univ.sum
          (fun x : α × (β × γ) =>
            if x.2.2 = γ0 ∧ P x.1 x.2.1 then
              F x.1 x.2.1 * u
            else
              0)
          =
          ∑ a : α, ∑ y : β × γ,
            if y.2 = γ0 ∧ P a y.1 then F a y.1 * u else 0 := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          ∑ a : α, ∑ b : β, ∑ c : γ,
            if c = γ0 ∧ P a b then F a b * u else 0 := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          Finset.univ.sum
            (fun a : α =>
              Finset.univ.sum
                (fun b : β =>
                  if P a b then F a b * u else 0)) := by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hP : P a b
            · rw [if_pos hP]
              rw [Finset.sum_eq_single γ0]
              · simp [hP]
              · intro c hc hne
                simp [hne, hP]
              · intro hnot
                exact False.elim (hnot (Finset.mem_univ γ0))
            · rw [if_neg hP]
              apply Finset.sum_eq_zero
              intro c hc
              simp [hP]
  let IsOriented :
      Sum (Fin m × Fin m) (Fin m × Fin m) → Prop :=
    fun e =>
      match e with
      | Sum.inl q => q.1.val < q.2.val
      | Sum.inr q => q.1.val < q.2.val
  let edgeCoord :
      (e : Sum (Fin m × Fin m) (Fin m × Fin m)) →
        IsOriented e → GraphCoord :=
    fun e h =>
      match e with
      | Sum.inl q => Sum.inl ⟨q, h⟩
      | Sum.inr q => Sum.inr ⟨q, h⟩
  have hEdgeCoord_injective :
      ∀ {e₁ e₂ : Sum (Fin m × Fin m) (Fin m × Fin m)}
        {h₁ : IsOriented e₁} {h₂ : IsOriented e₂},
        edgeCoord e₁ h₁ = edgeCoord e₂ h₂ → e₁ = e₂ := by
    intro e₁ e₂ h₁ h₂ h
    cases e₁ with
    | inl q₁ =>
        cases e₂ with
        | inl q₂ =>
            simp [edgeCoord] at h
            injection h with hsub
            have hq : q₁ = q₂ := by
              simpa using congrArg Subtype.val hsub
            exact congrArg Sum.inl hq
        | inr q₂ =>
            simp [edgeCoord] at h
    | inr q₁ =>
        cases e₂ with
        | inl q₂ =>
            simp [edgeCoord] at h
        | inr q₂ =>
            simp [edgeCoord] at h
            injection h with hsub
            have hq : q₁ = q₂ := by
              simpa using congrArg Subtype.val hsub
            exact congrArg Sum.inr hq
  let recordedCoord : Finset GraphCoord :=
    recorded.attach.image
      (fun e => edgeCoord e.1 (hRecordedOriented e.1 e.2))
  let productCoord : Finset GraphCoord :=
    product.attach.image
      (fun e => edgeCoord e.1 (hProductOriented e.1 e.2))
  let ACoord : Finset GraphCoord :=
    A.attach.image
      (fun e => edgeCoord e.1 (hAOriented e.1 e.2))
  let coordTarget : GraphCoord → Bool :=
    fun c =>
      if c ∈ productCoord then
        decide (c ∈ ACoord)
      else
        graphPairBoolEquiv (ω0.1, ω0.2.1) c
  have hRecordedProductCoordDisjoint :
      Disjoint recordedCoord productCoord := by
    rw [Finset.disjoint_left]
    intro c hcRec hcProd
    rcases Finset.mem_image.mp hcRec with ⟨er, herMem, herEq⟩
    rcases Finset.mem_image.mp hcProd with ⟨ep, hepMem, hepEq⟩
    have heq : er.1 = ep.1 :=
      hEdgeCoord_injective (herEq.trans hepEq.symm)
    exact hProductUnrecorded ep.1 ep.2 (by simpa [heq] using er.2)
  have hACoord_mem_iff :
      ∀ {e : Sum (Fin m × Fin m) (Fin m × Fin m)}
        (heProduct : e ∈ product),
        edgeCoord e (hProductOriented e heProduct) ∈ ACoord ↔ e ∈ A := by
    intro e heProduct
    constructor
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨ea, heaMem, heaEq⟩
      have heq : ea.1 = e := hEdgeCoord_injective (heaEq)
      simpa [heq] using ea.2
    · intro heA
      have hcoord :
          edgeCoord e (hAOriented e heA) =
            edgeCoord e (hProductOriented e heProduct) := by
        cases e <;> simp [edgeCoord]
      exact
        Finset.mem_image.mpr
          ⟨⟨e, heA⟩, Finset.mem_attach _ _, hcoord⟩
  have hProductCoordProd :
      productCoord.prod (fun c => if coordTarget c then p else (1 : ℝ) - p) =
        p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) := by
    calc
      productCoord.prod (fun c => if coordTarget c then p else (1 : ℝ) - p)
          =
          product.prod (fun e =>
            if e ∈ A then p else (1 : ℝ) - p) := by
            unfold productCoord
            rw [Finset.prod_image]
            · calc
                (∏ x ∈ product.attach,
                    if coordTarget
                        (edgeCoord x.1 (hProductOriented x.1 x.2)) then
                      p
                    else
                      (1 : ℝ) - p)
                    =
                    ∏ x ∈ product.attach,
                      if x.1 ∈ A then p else (1 : ℝ) - p := by
                      apply Finset.prod_congr rfl
                      intro e he
                      have htarget :
                          coordTarget
                            (edgeCoord e.1 (hProductOriented e.1 e.2)) =
                            decide (e.1 ∈ A) := by
                        unfold coordTarget
                        have hmemProduct :
                            edgeCoord e.1 (hProductOriented e.1 e.2) ∈
                              product.attach.image
                                (fun e => edgeCoord e.1 (hProductOriented e.1 e.2)) :=
                          Finset.mem_image.mpr
                            ⟨e, Finset.mem_attach _ _, rfl⟩
                        rw [if_pos hmemProduct]
                        by_cases hAcoord :
                            edgeCoord e.1 (hProductOriented e.1 e.2) ∈ ACoord
                        · have heA : e.1 ∈ A := (hACoord_mem_iff e.2).1 hAcoord
                          simp [hAcoord, heA]
                        · have heNotA : e.1 ∉ A := by
                            intro heA
                            exact hAcoord ((hACoord_mem_iff e.2).2 heA)
                          simp [hAcoord, heNotA]
                      by_cases heA : e.1 ∈ A
                      · simp [htarget, heA]
                      · simp [htarget, heA]
                _ = product.prod
                    (fun e => if e ∈ A then p else (1 : ℝ) - p) := by
                      simpa using
                        (Finset.prod_attach product
                          (fun e => if e ∈ A then p else (1 : ℝ) - p))
            · intro x hx y hy hxy
              apply Subtype.ext
              exact hEdgeCoord_injective hxy
      _ = p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card) :=
            hFactorProduct
  have hUnionCoordProd :
      (recordedCoord ∪ productCoord).prod
          (fun c => if coordTarget c then p else (1 : ℝ) - p) =
        (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card)) *
          recordedCoord.prod
            (fun c => if coordTarget c then p else (1 : ℝ) - p) := by
    rw [Finset.prod_union hRecordedProductCoordDisjoint]
    rw [hProductCoordProd]
    ring
  let sampleFromPair :
      SimpleGraph (Fin m) × SimpleGraph (Fin m) → TwoBiteSample n m p :=
    fun x => (x.1, x.2, ω0.2.2)
  have hDecideEqIff :
      ∀ (P Q : Prop) [Decidable P] [Decidable Q],
        (decide P = decide Q) ↔ (P ↔ Q) := by
    intro P Q _ _
    by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
  have hEdgeCoordValueBool :
      ∀ (x : SimpleGraph (Fin m) × SimpleGraph (Fin m))
        (e : Sum (Fin m × Fin m) (Fin m × Fin m))
        (h : IsOriented e),
        graphPairBoolEquiv x (edgeCoord e h) =
          decide (TwoBiteEdgeCoordinateValue (sampleFromPair x) e) := by
    intro x e h
    cases e with
    | inl q =>
        simp [sampleFromPair, edgeCoord, graphPairBoolEquiv, graphBoolEquiv,
          TwoBiteEdgeCoordinateValue, TwoBiteRedGraph]
    | inr q =>
        simp [sampleFromPair, edgeCoord, graphPairBoolEquiv, graphBoolEquiv,
          TwoBiteEdgeCoordinateValue, TwoBiteBlueGraph]
  have hRecordedEventFixed :
      ∀ x : SimpleGraph (Fin m) × SimpleGraph (Fin m),
        recordedEvent (sampleFromPair x) ↔
          ∀ c, c ∈ recordedCoord →
            graphPairBoolEquiv x c = coordTarget c := by
    intro x
    constructor
    · intro hrec c hc
      rcases Finset.mem_image.mp hc with ⟨er, herMem, herEq⟩
      rw [← herEq]
      have hcRec :
          edgeCoord er.1 (hRecordedOriented er.1 er.2) ∈ recordedCoord :=
        Finset.mem_image.mpr ⟨er, Finset.mem_attach _ _, rfl⟩
      have hcNotProduct :
          edgeCoord er.1 (hRecordedOriented er.1 er.2) ∉ productCoord :=
        (Finset.disjoint_left.mp hRecordedProductCoordDisjoint) hcRec
      unfold coordTarget
      rw [if_neg hcNotProduct]
      rw [hEdgeCoordValueBool x er.1 (hRecordedOriented er.1 er.2)]
      have hω0 :
          graphPairBoolEquiv (ω0.1, ω0.2.1)
              (edgeCoord er.1 (hRecordedOriented er.1 er.2)) =
            decide (TwoBiteEdgeCoordinateValue ω0 er.1) := by
        simpa [sampleFromPair] using
          hEdgeCoordValueBool (ω0.1, ω0.2.1) er.1
            (hRecordedOriented er.1 er.2)
      rw [hω0]
      exact (hDecideEqIff
        (TwoBiteEdgeCoordinateValue (sampleFromPair x) er.1)
        (TwoBiteEdgeCoordinateValue ω0 er.1)).2 (hrec er.1 er.2)
    · intro hfix e he
      have hc :
          edgeCoord e (hRecordedOriented e he) ∈ recordedCoord :=
        Finset.mem_image.mpr
          ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩
      have hEq := hfix (edgeCoord e (hRecordedOriented e he)) hc
      have hcNotProduct :
          edgeCoord e (hRecordedOriented e he) ∉ productCoord :=
        (Finset.disjoint_left.mp hRecordedProductCoordDisjoint) hc
      unfold coordTarget at hEq
      rw [if_neg hcNotProduct] at hEq
      rw [hEdgeCoordValueBool x e (hRecordedOriented e he)] at hEq
      have hω0 :
          graphPairBoolEquiv (ω0.1, ω0.2.1)
              (edgeCoord e (hRecordedOriented e he)) =
            decide (TwoBiteEdgeCoordinateValue ω0 e) := by
        simpa [sampleFromPair] using
          hEdgeCoordValueBool (ω0.1, ω0.2.1) e
            (hRecordedOriented e he)
      rw [hω0] at hEq
      exact (hDecideEqIff
        (TwoBiteEdgeCoordinateValue (sampleFromPair x) e)
        (TwoBiteEdgeCoordinateValue ω0 e)).1 hEq
  have hProductEventFixed :
      ∀ x : SimpleGraph (Fin m) × SimpleGraph (Fin m),
        productEvent (sampleFromPair x) ↔
          ∀ c, c ∈ productCoord →
            graphPairBoolEquiv x c = coordTarget c := by
    intro x
    constructor
    · intro hprod c hc
      rcases Finset.mem_image.mp hc with ⟨ep, hepMem, hepEq⟩
      rw [← hepEq]
      have hcProduct :
          edgeCoord ep.1 (hProductOriented ep.1 ep.2) ∈ productCoord :=
        Finset.mem_image.mpr ⟨ep, Finset.mem_attach _ _, rfl⟩
      unfold coordTarget
      rw [if_pos hcProduct]
      rw [hEdgeCoordValueBool x ep.1 (hProductOriented ep.1 ep.2)]
      by_cases hAcoord :
          edgeCoord ep.1 (hProductOriented ep.1 ep.2) ∈ ACoord
      · have heA : ep.1 ∈ A := (hACoord_mem_iff ep.2).1 hAcoord
        simp [hAcoord, (hprod ep.1 ep.2).2 heA]
      · have heNotA : ep.1 ∉ A := by
          intro heA
          exact hAcoord ((hACoord_mem_iff ep.2).2 heA)
        have hnotEdge :
            ¬ TwoBiteEdgeCoordinateValue (sampleFromPair x) ep.1 := by
          intro hedge
          exact heNotA ((hprod ep.1 ep.2).1 hedge)
        simp [hAcoord, hnotEdge]
    · intro hfix e he
      have hc :
          edgeCoord e (hProductOriented e he) ∈ productCoord :=
        Finset.mem_image.mpr
          ⟨⟨e, he⟩, Finset.mem_attach _ _, rfl⟩
      have hEq := hfix (edgeCoord e (hProductOriented e he)) hc
      unfold coordTarget at hEq
      rw [if_pos hc] at hEq
      rw [hEdgeCoordValueBool x e (hProductOriented e he)] at hEq
      by_cases hAcoord :
          edgeCoord e (hProductOriented e he) ∈ ACoord
      · have heA : e ∈ A := (hACoord_mem_iff he).1 hAcoord
        simp [hAcoord] at hEq
        exact ⟨fun _ => heA, fun _ => hEq⟩
      · have heNotA : e ∉ A := by
          intro heA
          exact hAcoord ((hACoord_mem_iff he).2 heA)
        simp [hAcoord] at hEq
        have hnotEdge :
            ¬ TwoBiteEdgeCoordinateValue (sampleFromPair x) e := by
          exact hEq
        exact ⟨fun hedge => False.elim (hnotEdge hedge), fun heA => False.elim (heNotA heA)⟩
  have hNumeratorEventFixed :
      ∀ x : SimpleGraph (Fin m) × SimpleGraph (Fin m),
        productEvent (sampleFromPair x) ∧ recordedEvent (sampleFromPair x) ↔
          ∀ c, c ∈ recordedCoord ∪ productCoord →
            graphPairBoolEquiv x c = coordTarget c := by
    intro x
    constructor
    · intro hx c hc
      have hcCases := Finset.mem_union.mp hc
      cases hcCases with
      | inl hcRec => exact (hRecordedEventFixed x).1 hx.2 c hcRec
      | inr hcProd => exact (hProductEventFixed x).1 hx.1 c hcProd
    · intro hfix
      constructor
      · exact (hProductEventFixed x).2
          (by
            intro c hc
            exact hfix c (Finset.mem_union.mpr (Or.inr hc)))
      · exact (hRecordedEventFixed x).2
          (by
            intro c hc
            exact hfix c (Finset.mem_union.mpr (Or.inl hc)))
  have hInjectionEvent_iff :
      ∀ a : TwoBiteSample n m p,
        injectionEvent a ↔ a.2.2 = ω0.2.2 := by
    intro a
    constructor
    · intro h
      apply DFunLike.ext
      intro x
      exact h x
    · intro h x
      exact congrArg (fun f : Fin n ↪ (Fin m × Fin m) => f x) h
  have hProductEvent_injection_irrel :
      ∀ a : TwoBiteSample n m p,
        productEvent a ↔ productEvent (sampleFromPair (a.1, a.2.1)) := by
    intro a
    simp [productEvent, sampleFromPair, TwoBiteEdgeCoordinateValue,
      TwoBiteRedGraph, TwoBiteBlueGraph]
  have hRecordedEvent_injection_irrel :
      ∀ a : TwoBiteSample n m p,
        recordedEvent a ↔ recordedEvent (sampleFromPair (a.1, a.2.1)) := by
    intro a
    simp [recordedEvent, sampleFromPair, TwoBiteEdgeCoordinateValue,
      TwoBiteRedGraph, TwoBiteBlueGraph]
  refine ⟨hDenominatorNonzero, ?_⟩
  change
    TwoBiteEventProbability n m p (fun ω => productEvent ω ∧ hist ω) =
      (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card)) *
        TwoBiteEventProbability n m p hist
  rw [hNumeratorCylinder, hDenominatorCylinder]
  unfold TwoBiteEventProbability
  unfold TwoBiteSampleWeight
  unfold UniformInjectionWeight
  rw [Finset.sum_filter, Finset.sum_filter]
  let U : ℝ :=
    if Fintype.card (Fin n ↪ (Fin m × Fin m)) = 0 then
      0
    else
      ((Fintype.card (Fin n ↪ (Fin m × Fin m)) : ℝ)⁻¹)
  let pairWeight :
      SimpleGraph (Fin m) → SimpleGraph (Fin m) → ℝ :=
    fun GR GB => GnpGraphWeight p GR * GnpGraphWeight p GB
  let numeratorPairEvent :
      SimpleGraph (Fin m) → SimpleGraph (Fin m) → Prop :=
    fun GR GB =>
      productEvent (sampleFromPair (GR, GB)) ∧
        recordedEvent (sampleFromPair (GR, GB))
  let denominatorPairEvent :
      SimpleGraph (Fin m) → SimpleGraph (Fin m) → Prop :=
    fun GR GB => recordedEvent (sampleFromPair (GR, GB))
  have hNumeratorMass :
      (Finset.univ.sum
        (fun a : TwoBiteSample n m p =>
          if productEvent a ∧ injectionEvent a ∧ recordedEvent a then
            pairWeight a.1 a.2.1 * U
          else
            0)) =
        (recordedCoord ∪ productCoord).prod
            (fun c => if coordTarget c then p else (1 : ℝ) - p) * U := by
    calc
      (Finset.univ.sum
        (fun a : TwoBiteSample n m p =>
          if productEvent a ∧ injectionEvent a ∧ recordedEvent a then
            pairWeight a.1 a.2.1 * U
          else
            0))
          =
          Finset.univ.sum
            (fun a : TwoBiteSample n m p =>
              if a.2.2 = ω0.2.2 ∧ numeratorPairEvent a.1 a.2.1 then
                pairWeight a.1 a.2.1 * U
              else
                0) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hcond :
                (productEvent a ∧ injectionEvent a ∧ recordedEvent a) ↔
                  a.2.2 = ω0.2.2 ∧ numeratorPairEvent a.1 a.2.1 := by
              rw [hInjectionEvent_iff a, hProductEvent_injection_irrel a,
                hRecordedEvent_injection_irrel a]
              simp [numeratorPairEvent, and_assoc, and_comm]
            by_cases hleft :
                productEvent a ∧ injectionEvent a ∧ recordedEvent a
            · have hright := hcond.mp hleft
              simp [hleft, hright]
            · have hright :
                ¬(a.2.2 = ω0.2.2 ∧ numeratorPairEvent a.1 a.2.1) := by
                intro h
                exact hleft (hcond.mpr h)
              simp [hleft, hright]
      _ =
          Finset.univ.sum
            (fun GR : SimpleGraph (Fin m) =>
              Finset.univ.sum
                (fun GB : SimpleGraph (Fin m) =>
                  if numeratorPairEvent GR GB then
                    pairWeight GR GB * U
                  else
                    0)) := by
            calc
              (Finset.univ.sum
                (fun a : TwoBiteSample n m p =>
                  if a.2.2 = ω0.2.2 ∧ numeratorPairEvent a.1 a.2.1 then
                    pairWeight a.1 a.2.1 * U
                  else
                    0))
                  =
                  ∑ GR : SimpleGraph (Fin m),
                    ∑ y : SimpleGraph (Fin m) × (Fin n ↪ (Fin m × Fin m)),
                      if y.2 = ω0.2.2 ∧ numeratorPairEvent GR y.1 then
                        pairWeight GR y.1 * U
                      else
                        0 := by
                    rw [← Finset.univ_product_univ, Finset.sum_product]
              _ =
                  ∑ GR : SimpleGraph (Fin m), ∑ GB : SimpleGraph (Fin m),
                    ∑ c : Fin n ↪ (Fin m × Fin m),
                      if c = ω0.2.2 ∧ numeratorPairEvent GR GB then
                        pairWeight GR GB * U
                      else
                        0 := by
                    apply Finset.sum_congr rfl
                    intro GR hGR
                    rw [← Finset.univ_product_univ, Finset.sum_product]
              _ =
                  Finset.univ.sum
                    (fun GR : SimpleGraph (Fin m) =>
                      Finset.univ.sum
                        (fun GB : SimpleGraph (Fin m) =>
                          if numeratorPairEvent GR GB then
                            pairWeight GR GB * U
                          else
                            0)) := by
                    apply Finset.sum_congr rfl
                    intro GR hGR
                    apply Finset.sum_congr rfl
                    intro GB hGB
                    by_cases hP : numeratorPairEvent GR GB
                    · rw [if_pos hP]
                      rw [Finset.sum_eq_single ω0.2.2]
                      · simp [hP]
                      · intro c hc hne
                        simp [hne, hP]
                      · intro hnot
                        exact False.elim (hnot (Finset.mem_univ ω0.2.2))
                    · rw [if_neg hP]
                      apply Finset.sum_eq_zero
                      intro c hc
                      simp [hP]
      _ =
          Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if productEvent (sampleFromPair x) ∧
                  recordedEvent (sampleFromPair x) then
                pairWeight x.1 x.2 * U
              else
                0) := by
            set_option maxHeartbeats 1000000 in
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if
                  ∀ c, c ∈ recordedCoord ∪ productCoord →
                    graphPairBoolEquiv x c = coordTarget c
              then
                pairWeight x.1 x.2 * U
              else
                0) := by
            set_option maxHeartbeats 1000000 in
            apply Finset.sum_congr rfl
            intro x hx
            have hiff := hNumeratorEventFixed x
            by_cases hleft :
                productEvent (sampleFromPair x) ∧ recordedEvent (sampleFromPair x)
            · have hright := hiff.mp hleft
              rw [if_pos hleft]
              rw [if_pos hright]
            · have hright :
                ¬(∀ c, c ∈ recordedCoord ∪ productCoord →
                    graphPairBoolEquiv x c = coordTarget c) := by
                intro h
                exact hleft (hiff.mpr h)
              rw [if_neg hleft]
              rw [if_neg hright]
      _ =
          (recordedCoord ∪ productCoord).prod
              (fun c => if coordTarget c then p else (1 : ℝ) - p) * U := by
            set_option maxHeartbeats 1000000 in
            simpa only [pairWeight] using
              (hPairCylinderMassScalar
                (recordedCoord ∪ productCoord) coordTarget U)
  have hDenominatorMass :
      (Finset.univ.sum
        (fun a : TwoBiteSample n m p =>
          if injectionEvent a ∧ recordedEvent a then
            pairWeight a.1 a.2.1 * U
          else
            0)) =
        recordedCoord.prod
            (fun c => if coordTarget c then p else (1 : ℝ) - p) * U := by
    calc
      (Finset.univ.sum
        (fun a : TwoBiteSample n m p =>
          if injectionEvent a ∧ recordedEvent a then
            pairWeight a.1 a.2.1 * U
          else
            0))
          =
          Finset.univ.sum
            (fun a : TwoBiteSample n m p =>
              if a.2.2 = ω0.2.2 ∧ denominatorPairEvent a.1 a.2.1 then
                pairWeight a.1 a.2.1 * U
              else
                0) := by
            apply Finset.sum_congr rfl
            intro a ha
            have hcond :
                (injectionEvent a ∧ recordedEvent a) ↔
                  a.2.2 = ω0.2.2 ∧ denominatorPairEvent a.1 a.2.1 := by
              rw [hInjectionEvent_iff a, hRecordedEvent_injection_irrel a]
            by_cases hleft : injectionEvent a ∧ recordedEvent a
            · have hright := hcond.mp hleft
              simp [hleft, hright]
            · have hright :
                ¬(a.2.2 = ω0.2.2 ∧ denominatorPairEvent a.1 a.2.1) := by
                intro h
                exact hleft (hcond.mpr h)
              simp [hleft, hright]
      _ =
          Finset.univ.sum
            (fun GR : SimpleGraph (Fin m) =>
              Finset.univ.sum
                (fun GB : SimpleGraph (Fin m) =>
                  if denominatorPairEvent GR GB then
                    pairWeight GR GB * U
                  else
                    0)) := by
            calc
              (Finset.univ.sum
                (fun a : TwoBiteSample n m p =>
                  if a.2.2 = ω0.2.2 ∧ denominatorPairEvent a.1 a.2.1 then
                    pairWeight a.1 a.2.1 * U
                  else
                    0))
                  =
                  ∑ GR : SimpleGraph (Fin m),
                    ∑ y : SimpleGraph (Fin m) × (Fin n ↪ (Fin m × Fin m)),
                      if y.2 = ω0.2.2 ∧ denominatorPairEvent GR y.1 then
                        pairWeight GR y.1 * U
                      else
                        0 := by
                    rw [← Finset.univ_product_univ, Finset.sum_product]
              _ =
                  ∑ GR : SimpleGraph (Fin m), ∑ GB : SimpleGraph (Fin m),
                    ∑ c : Fin n ↪ (Fin m × Fin m),
                      if c = ω0.2.2 ∧ denominatorPairEvent GR GB then
                        pairWeight GR GB * U
                      else
                        0 := by
                    apply Finset.sum_congr rfl
                    intro GR hGR
                    rw [← Finset.univ_product_univ, Finset.sum_product]
              _ =
                  Finset.univ.sum
                    (fun GR : SimpleGraph (Fin m) =>
                      Finset.univ.sum
                        (fun GB : SimpleGraph (Fin m) =>
                          if denominatorPairEvent GR GB then
                            pairWeight GR GB * U
                          else
                            0)) := by
                    apply Finset.sum_congr rfl
                    intro GR hGR
                    apply Finset.sum_congr rfl
                    intro GB hGB
                    by_cases hP : denominatorPairEvent GR GB
                    · rw [if_pos hP]
                      rw [Finset.sum_eq_single ω0.2.2]
                      · simp [hP]
                      · intro c hc hne
                        simp [hne, hP]
                      · intro hnot
                        exact False.elim (hnot (Finset.mem_univ ω0.2.2))
                    · rw [if_neg hP]
                      apply Finset.sum_eq_zero
                      intro c hc
                      simp [hP]
      _ =
          Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if recordedEvent (sampleFromPair x) then
                pairWeight x.1 x.2 * U
              else
                0) := by
            set_option maxHeartbeats 1000000 in
            rw [← Finset.univ_product_univ, Finset.sum_product]
      _ =
          Finset.univ.sum
            (fun x : SimpleGraph (Fin m) × SimpleGraph (Fin m) =>
              if
                  ∀ c, c ∈ recordedCoord →
                    graphPairBoolEquiv x c = coordTarget c
              then
                pairWeight x.1 x.2 * U
              else
                0) := by
            set_option maxHeartbeats 1000000 in
            apply Finset.sum_congr rfl
            intro x hx
            have hiff := hRecordedEventFixed x
            by_cases hleft : recordedEvent (sampleFromPair x)
            · have hright := hiff.mp hleft
              rw [if_pos hleft]
              rw [if_pos hright]
            · have hright :
                ¬(∀ c, c ∈ recordedCoord →
                    graphPairBoolEquiv x c = coordTarget c) := by
                intro h
                exact hleft (hiff.mpr h)
              rw [if_neg hleft]
              rw [if_neg hright]
      _ =
          recordedCoord.prod
              (fun c => if coordTarget c then p else (1 : ℝ) - p) * U := by
            set_option maxHeartbeats 1000000 in
            simpa only [pairWeight] using
              (hPairCylinderMassScalar recordedCoord coordTarget U)
  have hFinal :
      (Finset.univ.sum
          (fun a : TwoBiteSample n m p =>
            if productEvent a ∧ injectionEvent a ∧ recordedEvent a then
              pairWeight a.1 a.2.1 * U
            else
              0)) =
        (p ^ A.card * ((1 : ℝ) - p) ^ (product.card - A.card)) *
          Finset.univ.sum
            (fun a : TwoBiteSample n m p =>
              if injectionEvent a ∧ recordedEvent a then
                pairWeight a.1 a.2.1 * U
              else
                0) := by
    rw [hNumeratorMass, hDenominatorMass, hUnionCoordProd]
    ring
  simpa [pairWeight, U] using hFinal
