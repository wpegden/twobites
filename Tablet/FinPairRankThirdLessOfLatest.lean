import Tablet.Preamble

-- [TABLET NODE: FinPairRankThirdLessOfLatest]

theorem FinPairRankThirdLessOfLatest {m : ℕ} {x y z : Fin m} :
    x ≠ y →
    (Nat.min x.val z.val * m + Nat.max x.val z.val <
      Nat.min x.val y.val * m + Nat.max x.val y.val) →
    (Nat.min y.val z.val * m + Nat.max y.val z.val <
      Nat.min x.val y.val * m + Nat.max x.val y.val) →
    z.val < x.val ∧ z.val < y.val := by
-- BODY
  intro hxy hzx hzy
  have hm_pos : 0 < m := by omega
  have hxy_val : x.val ≠ y.val := by
    intro h
    exact hxy (Fin.ext h)
  rcases lt_or_gt_of_ne hxy_val with hxy_lt | hyx_lt
  · have hzxlt : z.val < x.val := by
      by_contra hnot
      have hxz : x.val ≤ z.val := le_of_not_gt hnot
      have hmin_ge : x.val ≤ Nat.min y.val z.val :=
        le_min (le_of_lt hxy_lt) hxz
      have hmax_ge : y.val ≤ Nat.max y.val z.val := le_max_left _ _
      have hmul_ge : x.val * m ≤ Nat.min y.val z.val * m :=
        Nat.mul_le_mul_right m hmin_ge
      have hge_xy :
          x.val * m + y.val ≤
            Nat.min y.val z.val * m + Nat.max y.val z.val :=
        Nat.add_le_add hmul_ge hmax_ge
      have hpair_xy :
          Nat.min x.val y.val * m + Nat.max x.val y.val =
            x.val * m + y.val := by
        simp [Nat.min_eq_left (le_of_lt hxy_lt),
          Nat.max_eq_right (le_of_lt hxy_lt)]
      have hge_pair :
          Nat.min x.val y.val * m + Nat.max x.val y.val ≤
            Nat.min y.val z.val * m + Nat.max y.val z.val := by
        simpa [hpair_xy] using hge_xy
      exact (not_lt_of_ge hge_pair) hzy
    exact ⟨hzxlt, lt_trans hzxlt hxy_lt⟩
  · have hzylt : z.val < y.val := by
      by_contra hnot
      have hyz : y.val ≤ z.val := le_of_not_gt hnot
      have hmin_ge : y.val ≤ Nat.min x.val z.val :=
        le_min (le_of_lt hyx_lt) hyz
      have hmax_ge : x.val ≤ Nat.max x.val z.val := le_max_left _ _
      have hmul_ge : y.val * m ≤ Nat.min x.val z.val * m :=
        Nat.mul_le_mul_right m hmin_ge
      have hge_yx :
          y.val * m + x.val ≤
            Nat.min x.val z.val * m + Nat.max x.val z.val :=
        Nat.add_le_add hmul_ge hmax_ge
      have hpair_xy :
          Nat.min x.val y.val * m + Nat.max x.val y.val =
            y.val * m + x.val := by
        simp [Nat.min_eq_right (le_of_lt hyx_lt),
          Nat.max_eq_left (le_of_lt hyx_lt)]
      have hge_pair :
          Nat.min x.val y.val * m + Nat.max x.val y.val ≤
            Nat.min x.val z.val * m + Nat.max x.val z.val := by
        simpa [hpair_xy] using hge_yx
      exact (not_lt_of_ge hge_pair) hzx
    exact ⟨lt_trans hzylt hyx_lt, hzylt⟩
