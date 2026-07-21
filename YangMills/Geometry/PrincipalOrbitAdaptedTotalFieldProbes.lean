/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedTotalField

namespace YangMills.Geometry.PrincipalOrbitAdaptedTotalField.Probes

open Set
open scoped Manifold ContDiff
open PrincipalOrbitAdapted
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP
noncomputable section
set_option maxHeartbeats 1000000

variable {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    (IG : ModelWithCorners ℝ EG HG) (IB : ModelWithCorners ℝ EB HB)
    (IP : ModelWithCorners ℝ EP HP)
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)

/-- An arbitrary total tangent receives the exact adapted local extension package. -/
theorem exact_principal_adapted_total_package
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (v : TangentSpace IP p) (X : GroupLieAlgebra IG G) :
    ∃ field : (q : P) → TangentSpace IP q,
      field p = v ∧ IsOpen (adaptedTotalSource (IB := IB) chart b) ∧
      p ∈ adaptedTotalSource (IB := IB) chart b ∧
      ManifoldTangentField.IsSmoothOn IP (adaptedTotalSource (IB := IB) chart b) field ∧
      (∀ g : G, principalRightTranslationDifferential smoothBundle p g (field p) =
        field (torsor.rightAction p g)) ∧
      VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
        field (adaptedTotalSource (IB := IB) chart b) p = 0 :=
  exists_principalAdaptedTotalField IG IB IP chart smoothBundle chart_mem b p hp hcoord v X

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Changing recovery of the prescribed tangent contradicts the exact inverse chart derivative. -/
theorem changed_prescribed_total_value_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (v : TangentSpace IP p)
    (changed : (let coordinate := (mfderivWithin IP (IB.prod IG) chart.toPartialHomeomorph
      chart.toPartialHomeomorph.source p v)
      adaptedTotalField IG IB IP chart b coordinate.1 coordinate.2 p ≠ v)) : False :=
  changed (adaptedTotalField_self IG IB IP chart smoothBundle chart_mem b p hp hcoord v)

omit [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EB] [FiniteDimensional ℝ EP]
    [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Changing all-orbit right transport contradicts the exact principal-coordinate law. -/
theorem changed_total_right_transport_blocked
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (u : TangentSpace IB b) (w : GroupLieAlgebra IG G) (g : G)
    (changed : principalRightTranslationDifferential smoothBundle p g
      (adaptedTotalField IG IB IP chart b u w p) ≠
        adaptedTotalField IG IB IP chart b u w (torsor.rightAction p g)) : False :=
  changed (adaptedTotalField_rightTranslation IG IB IP chart smoothBundle chart_mem
    b p hp hcoord u w g)

/-- A nonzero transported bracket contradicts the exact partial-trivialization calculation. -/
theorem nonzero_total_adapted_bracket_blocked
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (b : B) (p : P) (hp : p ∈ chart.toPartialHomeomorph.source)
    (hcoord : chart.toPartialHomeomorph p = (b, (1 : G)))
    (u : TangentSpace IB b) (X w : GroupLieAlgebra IG G)
    (nonzero : VectorField.mlieBracketWithin IP
      (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
      (adaptedTotalField IG IB IP chart b u w)
      (adaptedTotalSource (IB := IB) chart b) p ≠ 0) : False :=
  nonzero (mlieBracketWithin_principalFundamental_adaptedTotalField
    IG IB IP chart smoothBundle chart_mem b p hp hcoord u X w)

end

end YangMills.Geometry.PrincipalOrbitAdaptedTotalField.Probes
