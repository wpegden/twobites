import Tablet.RealChooseTwo

-- [TABLET NODE: RealChooseTwoSumBound]

theorem RealChooseTwoSumBound :
    ∀ r t : ℝ,
      RealChooseTwo (r + t) - RealChooseTwo r - RealChooseTwo t = r * t := by
-- BODY
  intro r t
  unfold RealChooseTwo
  ring
