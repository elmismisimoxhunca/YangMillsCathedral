/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormSmoothDescent

/-!
# Hostile probes for smooth principal two-form descent
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff Bundle Topology

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
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (form_smooth : form.IsSmooth
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)

/-- The selected descent cannot have a different coordinate in an arbitrary designated chart. -/
theorem replacement_selectedBaseForm_arbitraryChartCoordinate_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : Fin 2 → TangentSpace IB b)
    (mismatch :
      AdjointBundle.DifferentialForm.inCoordinates
          (PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form)
          chart hb v ≠
        YangMills.Mathematics.groupLieAlgebraModelEquiv IG
          (form (principalBundleLocalSection chart b)
            (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP)
              chart b (v i)))) : False :=
  mismatch (PrincipalTwoForm.selectedBaseForm_inCoordinates smoothBundle form horizontal
    equivariant chart chart_mem hb v)

/-- Smoothness cannot fail once the same principal form is smooth, horizontal, and right
adjoint-equivariant. -/
theorem nonsmooth_selectedBaseForm_blocked
    (form_smooth : form.IsSmooth
      (YangMills.Mathematics.groupLieAlgebraModelEquiv IG))
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (equivariant : PrincipalTwoForm.IsRightAdEquivariant smoothBundle form)
    (failure : ¬AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form)) : False :=
  failure (PrincipalTwoForm.selectedBaseForm_isSmooth smoothBundle form form_smooth
    horizontal equivariant)

/-- Smooth packaging cannot replace the exact pointwise selected descent. -/
theorem replacement_selectedBaseFormSmooth_carrier_blocked
    (mismatch :
      (PrincipalTwoForm.selectedBaseFormSmooth smoothBundle form form_smooth
        horizontal equivariant).toForm ≠
      PrincipalTwoForm.selectedBaseForm (IB := IB) (bundle := bundle) form) : False :=
  mismatch (PrincipalTwoForm.selectedBaseFormSmooth_toForm smoothBundle form form_smooth
    horizontal equivariant)

end

end YangMills.Geometry.Probes
