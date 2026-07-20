/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleGaugeDiffeomorph

/-!
# Hostile probes for smooth gauge automorphisms of the adjoint quotient
-/

namespace YangMills.Geometry.AdjointBundleGaugeDiffeomorph.Probes

open Set
open scoped Manifold ContDiff
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
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

open SmoothGaugeTransformation

/-- The arbitrary-chart formula uses the exact forward `Ad(g_ϕ)` coefficient. -/
theorem exact_modelTrivialization_formula
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : B × EG)
    (hz : z ∈ (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).target) :
    AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
        (gauge.inducedAdjointBundleAction
          ((AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph.symm z)) =
      (z.1, lieGroupAdjointCoordinates (I := IG)
        (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2) :=
  gauge.inducedAdjointBundleAction_modelBundleTrivialization chart z hz

/-- The exact local model formula is smooth on the actual trivialization target. -/
theorem exact_modelFormula_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas) :
    ContMDiffOn (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      (fun z : B × EG =>
        (z.1, lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2))
      (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).target :=
  gauge.inducedAdjointBundleAction_modelFormula_contMDiffOn chart chart_mem

/-- The covariant quotient action is globally smooth in the named quotient atlas. -/
theorem exact_global_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      gauge.inducedAdjointBundleAction :=
  gauge.inducedAdjointBundleAction_contMDiff

/-- The inverse-gauge quotient action is smooth in exactly the same named atlas. -/
theorem exact_inverse_smoothness
    (gauge : SmoothGaugeTransformation smoothBundle) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
      gauge⁻¹.inducedAdjointBundleAction :=
  gauge.inducedAdjointBundleAction_inv_contMDiff

/-- Diffeomorphism packaging retains the exact quotient action carrier. -/
theorem exact_diffeomorphism_carrier
    (gauge : SmoothGaugeTransformation smoothBundle)
    (z : AdjointBundle (I := IG) torsor) :
    letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelChartedSpace (IG := IG) bundle
    letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
      AdjointBundle.modelIsManifold smoothBundle
    gauge.inducedAdjointBundleDiffeomorph z = gauge.inducedAdjointBundleAction z := rfl

/-- A nonsmooth induced action contradicts the exact local-coordinate globalization. -/
theorem nonsmooth_induced_action_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong :
      letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
        AdjointBundle.modelChartedSpace (IG := IG) bundle
      letI : IsManifold (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) :=
        AdjointBundle.modelIsManifold smoothBundle
      ¬ ContMDiff (IB.prod 𝓘(ℝ, EG)) (IB.prod 𝓘(ℝ, EG)) ∞
        gauge.inducedAdjointBundleAction) : False :=
  wrong gauge.inducedAdjointBundleAction_contMDiff

/-- A malformed local action formula is rejected on the exact chart target. -/
theorem malformed_model_formula_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (z : B × EG)
    (hz : z ∈ (AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).target)
    (wrong :
      AdjointBundle.modelBundleTrivialization (I := IG) bundle chart
          (gauge.inducedAdjointBundleAction
            ((AdjointBundle.modelBundleTrivialization (I := IG) bundle chart).toOpenPartialHomeomorph.symm z)) ≠
        (z.1, lieGroupAdjointCoordinates (I := IG)
          (gauge.associatedGaugeFunction (principalBundleLocalSection chart z.1)) z.2)) : False :=
  wrong (gauge.inducedAdjointBundleAction_modelBundleTrivialization chart z hz)

end

end YangMills.Geometry.AdjointBundleGaugeDiffeomorph.Probes
