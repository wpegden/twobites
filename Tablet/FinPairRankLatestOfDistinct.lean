import Tablet.Preamble

-- [TABLET NODE: FinPairRankLatestOfDistinct]

theorem FinPairRankLatestOfDistinct {m : ℕ} {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let pairRank : Fin m → Fin m → ℕ :=
      fun x y => Nat.min x.val y.val * m + Nat.max x.val y.val
    (pairRank a c < pairRank a b ∧ pairRank b c < pairRank a b) ∨
      (pairRank a b < pairRank a c ∧ pairRank b c < pairRank a c) ∨
      (pairRank a b < pairRank b c ∧ pairRank a c < pairRank b c) := by
-- BODY
  dsimp
  let pairRank : Fin m → Fin m → ℕ :=
    fun x y => Nat.min x.val y.val * m + Nat.max x.val y.val
  have hval_ab : a.val ≠ b.val := by
    intro h
    exact hab (Fin.ext h)
  have hval_ac : a.val ≠ c.val := by
    intro h
    exact hac (Fin.ext h)
  have hval_bc : b.val ≠ c.val := by
    intro h
    exact hbc (Fin.ext h)
  have rank_lt_of_min_lt {x y z t : Fin m}
      (hmin : Nat.min x.val y.val < Nat.min z.val t.val) :
      pairRank x y < pairRank z t := by
    have hmax_lt : Nat.max x.val y.val < m := max_lt x.is_lt y.is_lt
    have hstep1 : Nat.min x.val y.val * m + Nat.max x.val y.val <
        Nat.min x.val y.val * m + m :=
      Nat.add_lt_add_left hmax_lt (Nat.min x.val y.val * m)
    have hstep2 : Nat.min x.val y.val * m + m =
        (Nat.min x.val y.val + 1) * m := by
      rw [Nat.succ_mul]
    have hsucc_le : Nat.min x.val y.val + 1 ≤ Nat.min z.val t.val :=
      Nat.succ_le_of_lt hmin
    have hstep3 : (Nat.min x.val y.val + 1) * m ≤ Nat.min z.val t.val * m :=
      Nat.mul_le_mul_right m hsucc_le
    have hblock : Nat.min x.val y.val * m + Nat.max x.val y.val <
        Nat.min z.val t.val * m := by
      exact lt_of_lt_of_le (by simpa [hstep2] using hstep1) hstep3
    exact lt_of_lt_of_le hblock (Nat.le_add_right _ _)
  have hcase :
      (a.val < b.val ∧ a.val < c.val) ∨
        (b.val < a.val ∧ b.val < c.val) ∨
        (c.val < a.val ∧ c.val < b.val) := by
    omega
  rcases hcase with hamin | hbmin | hcmin
  · right
    right
    constructor
    · have hmin : Nat.min a.val b.val < Nat.min b.val c.val := by
        simp [Nat.min_eq_left (le_of_lt hamin.1), hamin.1, hamin.2]
      exact rank_lt_of_min_lt hmin
    · have hmin : Nat.min a.val c.val < Nat.min b.val c.val := by
        simp [Nat.min_eq_left (le_of_lt hamin.2), hamin.1, hamin.2]
      exact rank_lt_of_min_lt hmin
  · right
    left
    constructor
    · have hmin : Nat.min a.val b.val < Nat.min a.val c.val := by
        simp [Nat.min_eq_right (le_of_lt hbmin.1), hbmin.1, hbmin.2]
      exact rank_lt_of_min_lt hmin
    · have hmin : Nat.min b.val c.val < Nat.min a.val c.val := by
        simp [Nat.min_eq_left (le_of_lt hbmin.2), hbmin.1, hbmin.2]
      exact rank_lt_of_min_lt hmin
  · left
    constructor
    · have hmin : Nat.min a.val c.val < Nat.min a.val b.val := by
        simp [Nat.min_eq_right (le_of_lt hcmin.1), hcmin.1, hcmin.2]
      exact rank_lt_of_min_lt hmin
    · have hmin : Nat.min b.val c.val < Nat.min a.val b.val := by
        simp [Nat.min_eq_right (le_of_lt hcmin.2), hcmin.1, hcmin.2]
      exact rank_lt_of_min_lt hmin
