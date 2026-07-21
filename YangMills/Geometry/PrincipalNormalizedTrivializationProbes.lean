/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalNormalizedTrivialization

namespace YangMills.Geometry.PrincipalNormalizedTrivialization.Probes

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

omit [ENat.LEInfty (minSmoothness ℝ 3)] in
/-- Normalization cannot retain a nonidentity group coordinate at its center. -/
theorem nonidentity_normalized_coordinate_blocked
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P)
    (hp : p ∈ chart.toPartialHomeomorph.source)
    (changed : (chart.normalizeAt p).toPartialHomeomorph p ≠
      (torsor.projection p, (1 : G))) : False :=
  changed (chart.normalizeAt_self p hp)

/-- Each arbitrary point and tangent receives an adapted package on one exact open source. -/
theorem arbitrary_point_exact_adapted_package
    (p : P) (v : TangentSpace IP p) (X : GroupLieAlgebra IG G) :
    ∃ (U : Set P) (field : (q : P) → TangentSpace IP q),
      IsOpen U ∧ p ∈ U ∧ field p = v ∧
      ManifoldTangentField.IsSmoothOn IP U field ∧
      (∀ g : G, principalRightTranslationDifferential smoothBundle p g (field p) =
        field (torsor.rightAction p g)) ∧
      VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X) field U p = 0 :=
  exists_principalAdaptedTotalField_arbitrary IG IB IP smoothBundle p v X

/-- A hostile assertion that every candidate either changes the value or has nonzero bracket is
incompatible with the constructed arbitrary-point package. -/
theorem arbitrary_point_failure_dichotomy_blocked
    (p : P) (v : TangentSpace IP p) (X : GroupLieAlgebra IG G)
    (hostile : ∀ (U : Set P) (field : (q : P) → TangentSpace IP q),
      IsOpen U → p ∈ U → ManifoldTangentField.IsSmoothOn IP U field →
      (∀ g : G, principalRightTranslationDifferential smoothBundle p g (field p) =
        field (torsor.rightAction p g)) →
      field p ≠ v ∨ VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X) field U p ≠ 0) : False := by
  obtain ⟨U, field, hopen, hp, hvalue, hsmooth, hright, hbracket⟩ :=
    exists_principalAdaptedTotalField_arbitrary IG IB IP smoothBundle p v X
  rcases hostile U field hopen hp hsmooth hright with hchanged | hnonzero
  · exact hchanged hvalue
  · exact hnonzero hbracket

end

end YangMills.Geometry.PrincipalNormalizedTrivialization.Probes
