/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalTwoFormLiftIndependence

/-!
# Hostile probes for lift independence of horizontal principal two-forms
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

/-- A vertical change in one argument cannot alter a horizontal two-form. -/
theorem verticalReplacement_changes_horizontalTwoForm_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (p : P) (args : Fin 2 → TangentSpace IP p) (i : Fin 2)
    (replacement : TangentSpace IP p)
    (verticalDifference :
      mfderiv IP IB torsor.projection p (args i - replacement) = 0)
    (mismatch : form p args ≠ form p (Function.update args i replacement)) : False :=
  mismatch (horizontal.eq_update_of_verticalDifference smoothBundle form p args i replacement
    verticalDifference)

/-- Two ordered tangent lifts with identical projections cannot give different horizontal-form
values at the same total-space point. -/
theorem sameProjection_different_horizontalTwoFormValue_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (p : P) (first second : Fin 2 → TangentSpace IP p)
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection p (first i) =
        mfderiv IP IB torsor.projection p (second i))
    (mismatch : form p first ≠ form p second) : False :=
  mismatch (horizontal.eq_of_projection_eq smoothBundle form p first second sameProjection)

/-- Arbitrary lifts cannot disagree with the exact designated local tangent lifts for a horizontal
form. -/
theorem arbitraryLift_disagrees_with_localTangentLift_blocked
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P
      (GroupLieAlgebra IG G) 2)
    (horizontal : PrincipalTwoForm.IsHorizontal smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (baseVectors : Fin 2 → TangentSpace IB b)
    (lifts : Fin 2 → TangentSpace IP (principalBundleLocalSection chart b))
    (lifts_project : ∀ i,
      mfderiv IP IB torsor.projection (principalBundleLocalSection chart b) (lifts i) =
        baseVectors i)
    (mismatch : form (principalBundleLocalSection chart b) lifts ≠
      form (principalBundleLocalSection chart b)
        (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b
          (baseVectors i))) : False :=
  mismatch (horizontal.eq_localTangentLift smoothBundle form chart chart_mem hb
    baseVectors lifts lifts_project)

end

end YangMills.Geometry.Probes
