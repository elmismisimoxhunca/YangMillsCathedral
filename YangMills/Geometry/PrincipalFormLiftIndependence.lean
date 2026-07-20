/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLift
import YangMills.Mathematics.ManifoldDifferentialForms
import YangMills.Mathematics.ContinuousAlternatingMapProjectionIndependence

/-!
# Arbitrary-degree horizontal principal forms and lift independence

Horizontality is defined for fixed-value principal differential forms of every degree. A finite
multilinear telescoping theorem proves that horizontal forms depend only on the projected base
vectors, so arbitrary lifts agree with the canonical designated local tangent lifts. This module
constructs no quotient descent or representative independence.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

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
    {V : Type uV} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

/-- A principal-space form of arbitrary degree and fixed-value codomain is horizontal when it
vanishes whenever any tangent argument is vertical for the bundle projection. -/
def PrincipalForm.IsHorizontal {k : ℕ}
    (_smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k) : Prop :=
  ∀ (p : P) (v : Fin k → TangentSpace IP p),
    (∃ i, mfderiv IP IB torsor.projection p (v i) = 0) → form p v = 0

namespace PrincipalForm.IsHorizontal

/-- Replacing one tangent argument by one with vertically differing projection leaves a horizontal
principal form unchanged, in arbitrary degree. -/
theorem eq_update_of_verticalDifference {k : ℕ}
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (p : P) (args : Fin k → TangentSpace IP p) (i : Fin k)
    (replacement : TangentSpace IP p)
    (verticalDifference :
      mfderiv IP IB torsor.projection p (args i - replacement) = 0) :
    form p args = form p (Function.update args i replacement) := by
  exact (form p).eq_update_of_sub_mem_ker
    (mfderiv IP IB torsor.projection p).toLinearMap (horizontal p) args i replacement
      verticalDifference

/-- At a fixed total-space point, a horizontal form of arbitrary degree takes the same value on any
two tuples of tangent lifts with the same projected base vectors. -/
theorem eq_of_projection_eq {k : ℕ}
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (p : P) (first second : Fin k → TangentSpace IP p)
    (sameProjection : ∀ i,
      mfderiv IP IB torsor.projection p (first i) =
        mfderiv IP IB torsor.projection p (second i)) :
    form p first = form p second := by
  exact (form p).eq_of_linearMap_apply_eq
    (mfderiv IP IB torsor.projection p).toLinearMap (horizontal p) first second sameProjection

/-- Any lifts at the point of a designated local section give the same horizontal-form value as the
canonical derivative lifts from that section, in arbitrary degree. -/
theorem eq_localTangentLift {k : ℕ}
    (form : YangMills.Mathematics.ManifoldDifferentialForm IP P V k)
    (horizontal : PrincipalForm.IsHorizontal smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet)
    (baseVectors : Fin k → TangentSpace IB b)
    (lifts : Fin k → TangentSpace IP (principalBundleLocalSection chart b))
    (lifts_project : ∀ i,
      mfderiv IP IB torsor.projection (principalBundleLocalSection chart b) (lifts i) =
        baseVectors i) :
    form (principalBundleLocalSection chart b) lifts =
      form (principalBundleLocalSection chart b)
        (fun i => principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b
          (baseVectors i)) := by
  apply eq_of_projection_eq smoothBundle form horizontal
  intro i
  rw [lifts_project i]
  exact (principalBundleLocalTangentLift_rightInverse
    smoothBundle chart chart_mem hb) (baseVectors i) |>.symm

end PrincipalForm.IsHorizontal

end
end YangMills.Geometry
