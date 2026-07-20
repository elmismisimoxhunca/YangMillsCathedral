/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormSmoothDescent

/-!
# Hostile probes for arbitrary-degree tensorial principal-form descent
-/

namespace YangMills.Geometry.PrincipalFormSmoothDescent.Probes

open Set
open scoped Manifold ContDiff Bundle Topology
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Degree-three descent lands in the actual dependent quotient fiber and has exact chart coordinates. -/
theorem exact_degree_three_coordinates
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 3)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 3 → TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle) form) chart hb v =
      groupLieAlgebraModelEquiv IG
        (form (principalBundleLocalSection chart b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i))) :=
  PrincipalForm.selectedBaseForm_inCoordinates smoothBundle form horizontal equivariant
    chart chart_mem hb v

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The degree-three value retains its exact representative in the actual adjoint quotient. -/
theorem exact_degree_three_quotient_representative
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 3)
    (b : B) (v : Fin 3 → TangentSpace IB b) :
    ((PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle) form b) v).1 =
      AdjointBundle.mk torsor
        (principalBundleLocalSection (bundle.trivializationAt b) b)
        (form (principalBundleLocalSection (bundle.trivializationAt b) b)
          (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
            (bundle.trivializationAt b) b (v i))) :=
  PrincipalForm.selectedBaseForm_quotient (IB := IB) (bundle := bundle) form b v

/-- Arbitrary-degree smooth tensorial forms produce genuine smooth adjoint-bundle forms. -/
noncomputable def exact_generic_smooth_descent
    {k : ℕ}
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) k)
    (form_smooth : form.IsSmooth (groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle k :=
  PrincipalForm.selectedBaseFormSmooth smoothBundle form form_smooth horizontal equivariant

/-- Degree-two predicates and selected carriers remain definitionally compatible. -/
theorem exact_degree_two_descent_compatibility
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 2) :
    PrincipalForm.IsRightAdEquivariant smoothBundle form ↔
      PrincipalTwoForm.IsRightAdEquivariant smoothBundle form :=
  Iff.rfl

omit [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The generic degree-two selected carrier is definitionally the existing carrier. -/
theorem exact_degree_two_selected_carrier_compatibility
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 2) :
    PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle) form =
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form :=
  rfl

/-- A changed degree-three chart coordinate contradicts representative-independent descent. -/
theorem mismatched_degree_three_coordinate_blocked
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 3)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalForm.IsRightAdEquivariant smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 3 → TangentSpace IB b)
    (wrong :
      AdjointBundle.DifferentialForm.inCoordinates
          (PrincipalForm.selectedBaseForm (IB := IB) (bundle := bundle) form) chart hb v ≠
        groupLieAlgebraModelEquiv IG
          (form (principalBundleLocalSection chart b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b (v i)))) : False :=
  wrong (PrincipalForm.selectedBaseForm_inCoordinates smoothBundle form horizontal equivariant
    chart chart_mem hb v)

end

end YangMills.Geometry.PrincipalFormSmoothDescent.Probes
