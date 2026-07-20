/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedProductField

namespace YangMills.Geometry.PrincipalOrbitAdaptedProductField.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics
open PrincipalOrbitAdapted

universe uE uH uG uEB uHB uB

noncomputable section

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Normalization recovers an arbitrary prescribed group tangent exactly. -/
theorem exact_group_tangent_recovery (h : G) (w : TangentSpace I h) :
    mulRightInvariantVectorField I (rightInvariantGeneratorAt I h w) h = w :=
  mulRightInvariantVectorField_rightInvariantGeneratorAt I h w

/-- The prescribed group tangent obeys exact right-translation transport. -/
theorem exact_group_right_transport (h g : G) (w : TangentSpace I h) :
    mfderiv I I (fun q : G => q * g) h w =
      mulRightInvariantVectorField I (rightInvariantGeneratorAt I h w) (h * g) :=
  rightInvariantGeneratorAt_rightTranslation I h g w

/-- The normalized fundamental/adapted fiber fields commute at the identity. -/
theorem exact_normalized_fiber_bracket
    [FiniteDimensional ℝ E] [ENat.LEInfty (minSmoothness ℝ 3)]
    (X w : GroupLieAlgebra I G) :
    VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I (rightInvariantGeneratorAt I 1 w)) 1 = 0 :=
  normalizedFundamental_adapted_bracket_zero I X w

variable {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {B : Type uB} [TopologicalSpace B]
    (IB : ModelWithCorners ℝ EB HB)
    [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- The product field has the exact prescribed pair and all-orbit transport law. -/
theorem exact_adapted_product_package
    (b : B) (u : TangentSpace IB b) (h : G) (w : TangentSpace I h) :
    ∃ field : (z : B × G) → TangentSpace (IB.prod I) z,
      field (b, h) = (u, w) ∧
      ManifoldTangentField.IsSmoothOn (IB.prod I)
        ((extChartAt IB b).source ×ˢ (Set.univ : Set G)) field ∧
      ∀ g : G,
        mfderiv (IB.prod I) (IB.prod I) (fun z : B × G => (z.1, z.2 * g)) (b, h)
          (field (b, h)) = field (b, h * g) :=
  exists_adaptedProductField I IB b u h w

omit [FiniteDimensional ℝ EB] in
/-- A changed value at the prescribed center contradicts the exact product construction. -/
theorem changed_adapted_product_value_blocked
    (b : B) (u : TangentSpace IB b) (h : G) (w : TangentSpace I h)
    (changed : adaptedProductField I IB b u h w (b, h) ≠ (u, w)) : False :=
  changed (adaptedProductField_self I IB b u h w)

end

end YangMills.Geometry.PrincipalOrbitAdaptedProductField.Probes
