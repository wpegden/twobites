import Tablet.ProjectionFiberCardBound

-- [TABLET NODE: NormalizePairImageCardBound]

theorem NormalizePairImageCardBound {m : ℕ}
    (S : Finset (Fin m × Fin m)) :
    let normalize : Fin m × Fin m → Fin m × Fin m :=
      fun e => if e.1.val < e.2.val then e else (e.2, e.1)
    (S.card : ℝ) ≤ 2 * (((S.image normalize).card : ℕ) : ℝ) := by
-- BODY
  classical
  intro normalize
  refine ProjectionFiberCardBound S normalize 2 ?_
  intro y hy
  have hsubset :
      S.filter (fun e => normalize e = y) ⊆
        ({y, (y.2, y.1)} : Finset (Fin m × Fin m)) := by
    intro e he
    rw [Finset.mem_filter] at he
    have hnorm : normalize e = y := he.2
    change (if e.1.val < e.2.val then e else (e.2, e.1)) = y at hnorm
    by_cases hlt : e.1.val < e.2.val
    · have heq : e = y := by
        simpa [hlt] using hnorm
      simp [heq]
    · have hswap : (e.2, e.1) = y := by
        simpa [hlt] using hnorm
      have heq : e = (y.2, y.1) := by
        exact Prod.ext (congrArg Prod.snd hswap) (congrArg Prod.fst hswap)
      simp [heq]
  have hcard_nat :
      (S.filter (fun e => normalize e = y)).card ≤
        ({y, (y.2, y.1)} : Finset (Fin m × Fin m)).card :=
    Finset.card_le_card hsubset
  have htwo_nat :
      ({y, (y.2, y.1)} : Finset (Fin m × Fin m)).card ≤ 2 := by
    calc
      ({y, (y.2, y.1)} : Finset (Fin m × Fin m)).card
          ≤ ({(y.2, y.1)} : Finset (Fin m × Fin m)).card + 1 := by
            simpa using
              (Finset.card_insert_le y ({(y.2, y.1)} : Finset (Fin m × Fin m)))
      _ = 2 := by simp
  exact_mod_cast le_trans hcard_nat htwo_nat
