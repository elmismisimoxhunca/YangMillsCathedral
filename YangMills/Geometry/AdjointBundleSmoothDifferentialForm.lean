/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDifferentialForm

/-!
# Smooth adjoint-bundle-valued differential forms

Smoothness is tested in every designated exact adjoint-bundle chart after evaluation on tuples of
locally smooth tangent-vector fields. This is the varying-fiber analogue of the project's
fixed-value smooth differential-form predicate and does not construct a replacement bundle of
alternating maps.

No covariant derivative, principal-form correspondence, or curvature descent is asserted.
-/

namespace YangMills.Geometry

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

namespace AdjointBundle.DifferentialForm

variable {k : ℕ}

/-- Evaluate a varying-fiber form on tangent fields and express the result in one totalized
transported chart. On the chart base set this is the exact fiber coordinate. -/
def coordinateEvaluation
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (fields : Fin k → (b : B) → TangentSpace IB b) (b : B) : EG :=
  ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart)
    ⟨b, (form b) (fun i => fields i b)⟩).2

omit [IsManifold IB ∞ B] in
/-- On a chart's base set, totalized coordinate evaluation is exactly postcomposition with the
quotient-derived continuous linear fiber coordinate. -/
@[simp]
theorem coordinateEvaluation_eq_inCoordinates
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (fields : Fin k → (b : B) → TangentSpace IB b)
    {b : B} (hb : b ∈ chart.baseSet) :
    coordinateEvaluation form chart fields b =
      inCoordinates form chart hb (fun i => fields i b) :=
  rfl

/-- Smoothness in the exact designated adjoint atlas, tested by local smooth tangent-field
evaluation. -/
def IsSmooth
    (_smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k) : Prop :=
  ∀ (chart : PrincipalBundleLocalTrivialization torsor),
    chart ∈ bundle.trivializationAtlas →
    ∀ (s : Set B) (fields : Fin k → (b : B) → TangentSpace IB b),
      s ⊆ chart.baseSet →
      (∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, EB)) ∞
        (fun b => (⟨b, fields i b⟩ : TangentBundle IB B)) s) →
      ContMDiffOn IB 𝓘(ℝ, EG) ∞
        (coordinateEvaluation form chart fields) s

/-- A pointwise adjoint-bundle-valued form bundled with genuine local smoothness in every exact
atlas chart. -/
structure Smooth
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (k : ℕ) where
  /-- Underlying pointwise varying-fiber differential form. -/
  toForm : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle k
  /-- Local smoothness in the exact transported atlas. -/
  smooth : IsSmooth smoothBundle toForm

namespace Smooth

/-- The smooth zero adjoint-bundle-valued form in every degree. -/
def zero (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (k : ℕ) :
    Smooth smoothBundle k where
  toForm := AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k
  smooth := by
    intro chart chart_mem s fields hs fields_smooth
    have zeroSmooth : ContMDiffOn IB 𝓘(ℝ, EG) ∞ (fun _ : B => (0 : EG)) s :=
      contMDiff_const.contMDiffOn
    refine zeroSmooth.congr ?_
    intro b hb
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    rw [coordinateEvaluation_eq_inCoordinates _ chart fields (hs hb)]
    change (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart (hs hb))
      ((AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k b)
        (fun i => fields i b)) = 0
    rw [AdjointBundle.DifferentialForm.zero_apply]
    exact map_zero _

/-- The bundled zero form retains the exact pointwise zero carrier. -/
@[simp]
theorem zero_toForm
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) (k : ℕ) :
    (zero smoothBundle k).toForm =
      AdjointBundle.DifferentialForm.zero (IG := IG) (IB := IB) bundle k :=
  rfl

end Smooth

end AdjointBundle.DifferentialForm

end

end YangMills.Geometry
