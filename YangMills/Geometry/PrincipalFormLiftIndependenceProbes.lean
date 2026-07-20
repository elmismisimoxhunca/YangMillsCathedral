/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalFormLiftIndependence
import YangMills.Geometry.PrincipalTwoFormLiftIndependence

/-!
# Hostile probes for arbitrary-degree principal lift independence
-/

namespace YangMills.Geometry.PrincipalFormLiftIndependence.Probes

open Set
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uEG uHG uEB uHB uEP uHP uG uB uP uV

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
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

/-- Arbitrary-degree horizontal forms agree on every pair of equally projected lift tuples. -/
theorem exact_generic_projection_independence
    {k : ℕ} (form : ManifoldDifferentialForm IP P V k)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (p : P) (first second : Fin k → TangentSpace IP p)
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection p (first i) =
        mfderiv IP IB torsor.projection p (second i)) :
    form p first = form p second :=
  horizontal.eq_of_projection_eq smoothBundle form p first second sameProjection

/-- Degree three explicitly exercises the generic path beyond the old degree-two implementation. -/
theorem exact_degree_three_local_lifts
    (form : ManifoldDifferentialForm IP P V 3)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (baseVectors : Fin 3 → TangentSpace IB b)
    (lifts : Fin 3 → TangentSpace IP (principalBundleLocalSection chart b))
    (lifts_project : ∀ i,
      mfderiv IP IB torsor.projection (principalBundleLocalSection chart b) (lifts i) =
        baseVectors i) :
    form (principalBundleLocalSection chart b) lifts =
      form (principalBundleLocalSection chart b)
        (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b
          (baseVectors i)) :=
  horizontal.eq_localTangentLift smoothBundle form chart chart_mem hb baseVectors lifts lifts_project

/-- The existing degree-two horizontality predicate is definitionally the generic specialization. -/
theorem exact_degree_two_horizontal_compatibility
    (form : ManifoldDifferentialForm IP P (GroupLieAlgebra IG G) 2) :
    PrincipalTwoForm.IsHorizontal smoothBundle form ↔
      PrincipalForm.IsHorizontal smoothBundle form :=
  Iff.rfl

/-- A changed value on equally projected arbitrary-degree lifts is rejected. -/
theorem mismatched_generic_lift_value_blocked
    {k : ℕ} (form : ManifoldDifferentialForm IP P V k)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (p : P) (first second : Fin k → TangentSpace IP p)
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection p (first i) =
        mfderiv IP IB torsor.projection p (second i))
    (wrong : form p first ≠ form p second) : False :=
  wrong (horizontal.eq_of_projection_eq smoothBundle form p first second sameProjection)

end

end YangMills.Geometry.PrincipalFormLiftIndependence.Probes
