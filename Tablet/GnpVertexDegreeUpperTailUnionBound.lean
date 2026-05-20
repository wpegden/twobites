import Tablet.GnpVertexIncidentEdgeGeneratingFunction
import Tablet.GnpVertexDegreeMarkovTailBounds
import Tablet.GraphDegreeCount
import Mathlib.Tactic

open Classical

-- [TABLET NODE: GnpVertexDegreeUpperTailUnionBound]

theorem GnpVertexDegreeUpperTailUnionBound (m : ℕ) (p ε t : ℝ) (r : Fin m)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    (∑ G : SimpleGraph (Fin m),
      if (1 + ε) * p * (m : ℝ) ≤ (GraphDegreeCount G r : ℝ) then
        GnpGraphWeight p G else 0) ≤
      Real.exp (-(t * ((1 + ε) * p * (m : ℝ)))) *
        (1 - p + p * Real.exp t) ^
          ((Finset.univ.filter
            (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
              e.1.1 = r ∨ e.1.2 = r)).card)
    ∧
    (∑ G : SimpleGraph (Fin m),
      if (GraphDegreeCount G r : ℝ) ≤ (1 - ε) * p * (m : ℝ) then
        GnpGraphWeight p G else 0) ≤
      Real.exp (t * ((1 - ε) * p * (m : ℝ))) *
        (1 - p + p * Real.exp (-t)) ^
          ((Finset.univ.filter
            (fun e : {e : Fin m × Fin m // e.1.val < e.2.val} =>
              e.1.1 = r ∨ e.1.2 = r)).card) := by
-- BODY
  classical
  let E := {e : Fin m × Fin m // e.1.val < e.2.val}
  let incident : E → Prop := fun e => e.1.1 = r ∨ e.1.2 = r
  have hcard :
      ∀ G : SimpleGraph (Fin m),
        GraphDegreeCount G r =
          (Finset.univ.filter
            (fun e : E => incident e ∧ G.Adj e.1.1 e.1.2)).card := by
    intro G
    let s : Finset (Fin m) := Finset.univ.filter (fun w => G.Adj r w)
    let tt : Finset E := Finset.univ.filter
      (fun e : E => incident e ∧ G.Adj e.1.1 e.1.2)
    have hcard' : s.card = tt.card := by
      apply Finset.card_bij
        (i := fun w hw =>
          if h : r.val < w.val then
            (⟨(r, w), h⟩ : E)
          else
            (⟨(w, r), by
              have hwAdj : G.Adj r w := (Finset.mem_filter.mp hw).2
              have hneq : r ≠ w := SimpleGraph.ne_of_adj G hwAdj
              have hvalne : r.val ≠ w.val := by
                intro hval
                exact hneq (Fin.ext hval)
              have hle : w.val ≤ r.val := Nat.le_of_not_gt h
              exact lt_of_le_of_ne hle hvalne.symm⟩ : E))
      · intro w hw
        have hwAdj : G.Adj r w := (Finset.mem_filter.mp hw).2
        by_cases h : r.val < w.val
        · simp [tt, incident, h, hwAdj]
        · have hwAdj' : G.Adj w r := (G.adj_comm w r).2 hwAdj
          simp [tt, incident, h, hwAdj']
      · intro w1 hw1 w2 hw2 heq
        by_cases h1 : r.val < w1.val
        · by_cases h2 : r.val < w2.val
          · simpa [h1, h2] using congrArg (fun e : E => e.1.2) heq
          · have hp : (r, w1) = (w2, r) := by
              simpa [h1, h2] using congrArg Subtype.val heq
            have hw1r : w1 = r := congrArg Prod.snd hp
            subst w1
            omega
        · by_cases h2 : r.val < w2.val
          · have hp : (w1, r) = (r, w2) := by
              simpa [h1, h2] using congrArg Subtype.val heq
            have hw2r : w2 = r := (congrArg Prod.snd hp).symm
            subst w2
            omega
          · simpa [h1, h2] using congrArg (fun e : E => e.1.1) heq
      · intro e he
        rcases e with ⟨⟨a, b⟩, hab⟩
        simp only [tt, incident, Finset.mem_filter, Finset.mem_univ, true_and] at he
        rcases he with ⟨hinc, hadj⟩
        rcases hinc with ha | hb
        · subst a
          refine ⟨b, ?_, ?_⟩
          · simp [s, hadj]
          · have hlt : r.val < b.val := hab
            simp [hlt]
        · subst b
          refine ⟨a, ?_, ?_⟩
          · have hadj' : G.Adj r a := (G.adj_comm a r).1 hadj
            simp [s, hadj']
          · have hnlt : ¬ r.val < a.val := not_lt.mpr (Nat.le_of_lt hab)
            apply Subtype.ext
            simp [hnlt]
    simpa [GraphDegreeCount, s, tt, incident] using hcard'
  have hpoint :
      ∀ (u : ℝ) (G : SimpleGraph (Fin m)),
        Real.exp (u * (GraphDegreeCount G r : ℝ)) =
          ∏ e : E,
            if incident e then
              if G.Adj e.1.1 e.1.2 then Real.exp u else 1
            else 1 := by
    intro u G
    let presentIncident : E → Prop := fun e => incident e ∧ G.Adj e.1.1 e.1.2
    have hprod :
        (∏ e : E,
          if incident e then
            if G.Adj e.1.1 e.1.2 then Real.exp u else 1
          else 1) =
        ∏ e ∈ Finset.univ.filter presentIncident, Real.exp u := by
      calc
        (∏ e : E,
          if incident e then
            if G.Adj e.1.1 e.1.2 then Real.exp u else 1
          else 1)
          = ∏ e : E, if presentIncident e then Real.exp u else 1 := by
              apply Finset.prod_congr rfl
              intro e _
              by_cases hi : incident e
              · by_cases ha : G.Adj e.1.1 e.1.2
                · simp [presentIncident, hi, ha]
                · simp [presentIncident, hi, ha]
              · simp [presentIncident, hi]
        _ = ∏ e ∈ Finset.univ.filter presentIncident, Real.exp u := by
              exact (Finset.prod_filter presentIncident (fun _ => Real.exp u)).symm
    calc
      Real.exp (u * (GraphDegreeCount G r : ℝ))
        = Real.exp u ^ GraphDegreeCount G r := by
            rw [show u * (GraphDegreeCount G r : ℝ) =
                (GraphDegreeCount G r : ℝ) * u by ring]
            rw [Real.exp_nat_mul]
      _ = Real.exp u ^
          (Finset.univ.filter presentIncident).card := by
            rw [hcard G]
      _ = ∏ e ∈ Finset.univ.filter presentIncident, Real.exp u := by
            rw [Finset.prod_const]
      _ = ∏ e : E,
            if incident e then
              if G.Adj e.1.1 e.1.2 then Real.exp u else 1
            else 1 := by
            rw [hprod]
  have hmoment :
      ∀ u : ℝ,
        (∑ G : SimpleGraph (Fin m),
          Real.exp (u * (GraphDegreeCount G r : ℝ)) * GnpGraphWeight p G) =
        (1 - p + p * Real.exp u) ^
          ((Finset.univ.filter (fun e : E => incident e)).card) := by
    intro u
    calc
      (∑ G : SimpleGraph (Fin m),
        Real.exp (u * (GraphDegreeCount G r : ℝ)) * GnpGraphWeight p G)
        = ∑ G : SimpleGraph (Fin m),
          (∏ e : E,
            if incident e then
              if G.Adj e.1.1 e.1.2 then Real.exp u else 1
            else 1) * GnpGraphWeight p G := by
            apply Finset.sum_congr rfl
            intro G _
            rw [hpoint u G]
      _ = (1 - p + p * Real.exp u) ^
          ((Finset.univ.filter (fun e : E => incident e)).card) := by
            simpa [E, incident] using
              GnpVertexIncidentEdgeGeneratingFunction m p (Real.exp u) r
  constructor
  · have hmark :=
      (GnpVertexDegreeMarkovTailBounds m p t ((1 + ε) * p * (m : ℝ)) r hp0 hp1 ht).1
    rw [hmoment t] at hmark
    simpa [E, incident] using hmark
  · have hmark :=
      (GnpVertexDegreeMarkovTailBounds m p t ((1 - ε) * p * (m : ℝ)) r hp0 hp1 ht).2
    have hneg :
        (∑ G : SimpleGraph (Fin m),
          Real.exp (-(t * (GraphDegreeCount G r : ℝ))) * GnpGraphWeight p G) =
        (1 - p + p * Real.exp (-t)) ^
          ((Finset.univ.filter (fun e : E => incident e)).card) := by
      calc
        (∑ G : SimpleGraph (Fin m),
          Real.exp (-(t * (GraphDegreeCount G r : ℝ))) * GnpGraphWeight p G)
          = ∑ G : SimpleGraph (Fin m),
              Real.exp ((-t) * (GraphDegreeCount G r : ℝ)) * GnpGraphWeight p G := by
                apply Finset.sum_congr rfl
                intro G _
                ring_nf
          _ = (1 - p + p * Real.exp (-t)) ^
              ((Finset.univ.filter (fun e : E => incident e)).card) := hmoment (-t)
    rw [hneg] at hmark
    simpa [E, incident] using hmark
