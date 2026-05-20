import Tablet.RealChooseTwo

-- [TABLET NODE: ProjectionOpenPairFunction]

noncomputable def ProjectionOpenPairFunction (ℓR ℓB k p n : ℝ) : ℝ :=
-- BODY
  RealChooseTwo ℓR + RealChooseTwo ℓB
    - min (RealChooseTwo (k - ℓR))
        (RealChooseTwo (p * n) + RealChooseTwo (k - ℓR - p * n))
    - min (RealChooseTwo (k - ℓB))
        (RealChooseTwo (p * n) + RealChooseTwo (k - ℓB - p * n))
