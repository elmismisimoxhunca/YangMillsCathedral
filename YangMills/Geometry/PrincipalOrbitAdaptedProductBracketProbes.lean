/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedProductBracket

namespace YangMills.Geometry.PrincipalOrbitAdaptedProductBracket.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics
open PrincipalOrbitAdapted

universe uE uH uG uEB uHB uB
noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {B : Type uB} [TopologicalSpace B]
    (IB : ModelWithCorners ℝ EB HB)
    [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- The exact product-manifold within bracket vanishes on the natural open domain at the center. -/
theorem exact_adapted_product_bracket
    (b : B) (u : TangentSpace IB b) (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracketWithin (IB.prod I)
        (fun z : B × G => (0, mulInvariantVectorField X z.2))
        (adaptedProductField I IB b u 1 Y)
        ((extChartAt IB b).source ×ˢ (Set.univ : Set G)) (b, 1) = 0 :=
  mlieBracketWithin_verticalFundamental_adaptedProductField_center I IB b u X Y

/-- A nonzero product bracket contradicts the factorwise chart calculation. -/
theorem nonzero_adapted_product_bracket_blocked
    (b : B) (u : TangentSpace IB b) (X Y : GroupLieAlgebra I G)
    (nonzero : VectorField.mlieBracketWithin (IB.prod I)
      (fun z : B × G => (0, mulInvariantVectorField X z.2))
      (adaptedProductField I IB b u 1 Y)
      ((extChartAt IB b).source ×ˢ (Set.univ : Set G)) (b, 1) ≠ 0) : False :=
  nonzero (mlieBracketWithin_verticalFundamental_adaptedProductField_center I IB b u X Y)

end

end YangMills.Geometry.PrincipalOrbitAdaptedProductBracket.Probes
