/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDegreeZeroForm
import YangMills.Geometry.AdjointBundlePrincipalCovariantDerivative

/-!
# Same-connection covariant exterior derivative in degree zero

Freed, immediately after equation (1.16), writes the connection covariant derivative as
`d_Θ = d + ad(Θ)`. The existing connection-indexed data implements this exact formula on dependent
adjoint sections. This module derives its canonical degree-zero-to-degree-one packaging in the
project's adjoint-bundle-valued differential-form carrier.

No new derivative is supplied: the resulting one-form evaluates definitionally to the same
Mathlib covariant derivative, and its designated-chart coordinate is therefore the existing exact
`dσ(X) + [A(X),σ]` expression for the same principal connection. This is only the degree-zero
endpoint. It does not define the positive-degree covariant exterior derivative or prove Bianchi.
-/

namespace YangMills.Geometry

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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- Package the exact same-connection covariant derivative of a degree-zero adjoint-valued form as
a degree-one adjoint-valued form. -/
def PrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 1 :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    exact ContinuousAlternatingMap.ofSubsingleton ℝ _ _ (0 : Fin 1)
      (data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b)

/-- Evaluation at the unique degree-one slot is definitionally the original intrinsic covariant
derivative on the exact section corresponding to the degree-zero form. -/
@[simp]
theorem PrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_apply
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (b : B) (v : Fin 1 → TangentSpace IB b) :
    (data.covariantExteriorDerivativeZero form b) v =
      data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b (v 0) := by
  rfl

/-- On a degree-zero form constructed from a section, evaluation recovers the covariant derivative
of that exact section with no replacement witness. -/
@[simp]
theorem PrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_ofSection
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (v : Fin 1 → TangentSpace IB b) :
    (data.covariantExteriorDerivativeZero
      (AdjointBundle.DifferentialForm.ofSection
        (IB := IB) (bundle := bundle) adjointSection) b) v =
      data.covariantDerivative adjointSection b (v 0) := by
  rw [data.covariantExteriorDerivativeZero_apply,
    AdjointBundle.DifferentialForm.toSection_ofSection]

/-- The evaluation law uniquely determines the packaged one-form, blocking an unrelated output. -/
theorem PrincipalConnectionAdjointCovariantDerivativeData.eq_covariantExteriorDerivativeZero_of_eval
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (other : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 1)
    (h : ∀ b X, (other b) (fun _ => X) =
      data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b X) :
    other = data.covariantExteriorDerivativeZero form := by
  funext b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun _ => v 0 := by
    funext i
    fin_cases i
    rfl
  rw [hv, h]
  rfl

/-- In every designated chart, the packaged one-form is exactly the same connection's local
`dσ + [A,σ]` expression. -/
theorem PrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_inCoordinates
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (form_smooth : AdjointBundle.DifferentialForm.IsSmooth smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) (v : Fin 1 → TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (data.covariantExteriorDerivativeZero form) chart hb v =
      connection.adjointLocalCovariantDerivativeExpression chart
        (AdjointBundle.DifferentialForm.toSection form) b (v 0) := by
  have section_smooth : AdjointBundle.Section.IsSmooth smoothBundle
      (AdjointBundle.DifferentialForm.toSection form) := by
    apply (AdjointBundle.DifferentialForm.isSmooth_ofSection_iff smoothBundle
      (AdjointBundle.DifferentialForm.toSection form)).mp
    simpa using form_smooth
  rw [AdjointBundle.DifferentialForm.inCoordinates_apply]
  change (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb)
      (data.covariantDerivative (AdjointBundle.DifferentialForm.toSection form) b (v 0)) = _
  exact data.coordinate_formula chart chart_mem _ section_smooth b hb (v 0)

/-- The local coordinate formula exposes the ordinary derivative and bracket correction from the
same principal connection rather than an unrelated connection field. -/
theorem PrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_eq_d_add_bracket
    {connection : PrincipalConnectionData smoothBundle}
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (form_smooth : AdjointBundle.DifferentialForm.IsSmooth smoothBundle form)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {b : B} (hb : b ∈ chart.baseSet) (v : Fin 1 → TangentSpace IB b) :
    AdjointBundle.DifferentialForm.inCoordinates
        (data.covariantExteriorDerivativeZero form) chart hb v =
      PrincipalConnectionData.adjointLocalOrdinaryDerivative
          (IG := IG) (IB := IB) (bundle := bundle) chart
          (AdjointBundle.DifferentialForm.toSection form) b (v 0) +
        connection.adjointLocalConnectionBracketTerm chart
          (AdjointBundle.DifferentialForm.toSection form) b (v 0) := by
  rw [data.covariantExteriorDerivativeZero_inCoordinates form form_smooth chart chart_mem hb v]
  rfl

end

end YangMills.Geometry
