/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothAtlas

/-!
# Hostile probes for the smooth adjoint quotient atlas
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff

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

include smoothBundle in
set_option backward.isDefEq.respectTransparency false in
/-- Any two designated model charts have transition in the exact smooth fiberwise-linear groupoid. -/
theorem designated_adjointBundle_transition_mem_groupoid
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas) :
    (AdjointBundle.modelBundleTrivialization (I := IG) bundle first).toOpenPartialHomeomorph.symm ≫ₕ
        (AdjointBundle.modelBundleTrivialization (I := IG) bundle second).toOpenPartialHomeomorph ∈
      contMDiffFiberwiseLinear B EG IB ∞ := by
  letI : ChartedSpace (B × EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.productChartedSpace (IG := IG) bundle
  letI : HasGroupoid (AdjointBundle (I := IG) torsor)
      (contMDiffFiberwiseLinear B EG IB ∞) :=
    AdjointBundle.productHasGroupoid smoothBundle
  exact StructureGroupoid.compatible (contMDiffFiberwiseLinear B EG IB ∞)
    (Set.mem_image_of_mem _ first_mem) (Set.mem_image_of_mem _ second_mem)

include smoothBundle in
/-- A designated transition cannot be rejected from the fiberwise-linear groupoid. -/
theorem nonfiberwiseLinear_adjointBundle_transition_blocked
    (first second : PrincipalBundleLocalTrivialization torsor)
    (first_mem : first ∈ bundle.trivializationAtlas)
    (second_mem : second ∈ bundle.trivializationAtlas)
    (rejected :
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle first).toOpenPartialHomeomorph.symm ≫ₕ
          (AdjointBundle.modelBundleTrivialization (I := IG) bundle second).toOpenPartialHomeomorph ∉
        contMDiffFiberwiseLinear B EG IB ∞) : False :=
  rejected (designated_adjointBundle_transition_mem_groupoid
    smoothBundle first second first_mem second_mem)

include smoothBundle in
/-- The named standard-model smooth manifold structure is constructible without a global instance. -/
theorem adjointBundle_modelIsManifold_available :
    Nonempty (@IsManifold ℝ _ (EB × EG) _ _ (ModelProd HB EG) _
      (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) _
      (AdjointBundle.modelChartedSpace (IG := IG) bundle)) :=
  ⟨AdjointBundle.modelIsManifold smoothBundle⟩

include smoothBundle in
/-- The named manifold structure and the original quotient-map theorem coexist on the same carrier
and topology; constructing the former does not require replacing the latter. -/
theorem adjointBundle_named_manifold_preserves_quotientMap :
    Nonempty (@IsManifold ℝ _ (EB × EG) _ _ (ModelProd HB EG) _
      (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) _
      (AdjointBundle.modelChartedSpace (IG := IG) bundle)) ∧
    Topology.IsQuotientMap
      (fun z : P × GroupLieAlgebra IG G => AdjointBundle.mk torsor z.1 z.2) :=
  ⟨⟨AdjointBundle.modelIsManifold smoothBundle⟩,
    AdjointBundle.mk_isQuotientMap (I := IG) (torsor := torsor)⟩

end

end YangMills.Geometry.Probes
