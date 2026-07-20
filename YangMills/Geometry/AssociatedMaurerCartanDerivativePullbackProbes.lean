/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AssociatedMaurerCartanDerivativePullback

/-!
# Hostile probes for the associated Maurer--Cartan derivative pullback
-/

namespace YangMills.Geometry.AssociatedMaurerCartanDerivativePullback.Probes

open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    [TopologicalSpace HG]
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
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- The associated derivative candidate is the exact pullback of the certified universal derivative. -/
theorem exact_associated_derivative_pullback
    (gauge : SmoothGaugeTransformation smoothBundle) :
    (associatedMaurerCartanDerivativeCandidate gauge).toForm =
      ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
        gauge.associatedGaugeFunction_contMDiff
        (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm :=
  associatedMaurerCartanDerivativeCandidate_eq_universal_pullback gauge

/-- An unrelated pulled derivative carrier is rejected. -/
theorem mismatched_associated_derivative_pullback_blocked
    (gauge : SmoothGaugeTransformation smoothBundle)
    (wrong :
      (associatedMaurerCartanDerivativeCandidate gauge).toForm ≠
        ManifoldDifferentialForm.pullback gauge.associatedGaugeFunction
          gauge.associatedGaugeFunction_contMDiff
          (leftMaurerCartanExteriorDerivative (IG := IG) (G := G)).toForm) : False :=
  wrong (associatedMaurerCartanDerivativeCandidate_eq_universal_pullback gauge)

end

end YangMills.Geometry.AssociatedMaurerCartanDerivativePullback.Probes
