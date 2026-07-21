/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalCommonAdaptedTotalFields

namespace YangMills.Geometry.PrincipalCommonAdaptedTotalFields.Probes

open Set
open scoped Manifold ContDiff
open PrincipalOrbitAdapted
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP uα
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

/-- Even an unrestricted index type receives one common exact open source. -/
theorem unrestricted_index_common_source
    {α : Type uα} (p : P) (X : GroupLieAlgebra IG G)
    (v : α → TangentSpace IP p) :
    ∃ (U : Set P) (fields : α → (q : P) → TangentSpace IP q),
      IsOpen U ∧ p ∈ U ∧ (∀ g, torsor.rightAction p g ∈ U) ∧
      (∀ i, fields i p = v i) ∧
      (∀ i, ManifoldTangentField.IsSmoothOn IP U (fields i)) ∧
      (∀ i g, principalRightTranslationDifferential smoothBundle p g (fields i p) =
        fields i (torsor.rightAction p g)) ∧
      (∀ i, VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
        (fields i) U p = 0) :=
  exists_common_principalAdaptedTotalFields_arbitrary IG IB IP smoothBundle p X v

/-- It is impossible that every common-source family changes a prescribed value or has a nonzero
fundamental-field bracket in some slot. -/
theorem common_source_failure_blocked
    {α : Type uα} [Nonempty α] (p : P) (X : GroupLieAlgebra IG G)
    (v : α → TangentSpace IP p)
    (hostile : ∀ (U : Set P) (fields : α → (q : P) → TangentSpace IP q),
      IsOpen U → p ∈ U → (∀ g, torsor.rightAction p g ∈ U) →
      (∀ i, ManifoldTangentField.IsSmoothOn IP U (fields i)) →
      (∀ i g, principalRightTranslationDifferential smoothBundle p g (fields i p) =
        fields i (torsor.rightAction p g)) →
      (∃ i, fields i p ≠ v i ∨ VectorField.mlieBracketWithin IP
        (principalFundamentalVectorField (smoothBundle := smoothBundle) X)
        (fields i) U p ≠ 0)) : False := by
  obtain ⟨U, fields, hopen, hp, horbit, hvalue, hsmooth, hright, hbracket⟩ :=
    exists_common_principalAdaptedTotalFields_arbitrary IG IB IP smoothBundle p X v
  obtain ⟨i, hchanged | hnonzero⟩ := hostile U fields hopen hp horbit hsmooth hright
  · exact hchanged (hvalue i)
  · exact hnonzero (hbracket i)

end

end YangMills.Geometry.PrincipalCommonAdaptedTotalFields.Probes
