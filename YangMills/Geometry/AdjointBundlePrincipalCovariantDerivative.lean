/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDependentFiberTopologicalModule
import YangMills.Geometry.AdjointBundleSection
import YangMills.Geometry.PointwisePrincipalConnection
import YangMills.Geometry.PrincipalBundleLocalTangentLift
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Adjoint-bundle covariant derivative tied to a principal connection

Immediately after Freed's equation (1.16), the connection covariant derivative is introduced as
`d_Θ = d + ad(Θ)`; equation (1.16) itself is the Bianchi identity.
Mathlib supplies the intrinsic Leibniz-law carrier for a covariant derivative on sections of a
vector bundle. This module specializes that carrier to the exact dependent adjoint bundle and
requires its value in every designated principal chart to equal the standard local expression

`dσ(X) + [A(X), σ]`.

The resulting structure is an uninhabited connection-indexed acceptance interface. It does not
construct the derivative, extend it to adjoint-valued differential forms, produce positive-order
curvature tensors, or prove Bianchi.
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
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG}
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HB B]
    {torsor : PrincipalBundleTorsorData G B P}

/-- Mathlib's bundled covariant-derivative carrier specialized to the exact dependent adjoint
bundle, with every algebraic and topological structure installed only inside the definition. -/
@[reducible] def AdjointBundle.CovariantDerivative
    (bundle : TopologicalPrincipalBundleData torsor) :=
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  letI (b : B) : IsTopologicalAddGroup
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberIsTopologicalAddGroup (IG := IG) bundle b
  letI (b : B) : ContinuousSMul ℝ
      (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberContinuousSMul (IG := IG) bundle b
  letI : TopologicalSpace
      (Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor))) :=
    AdjointBundle.dependentTotalSpaceTopology (I := IG) (torsor := torsor)
  letI : FiberBundle EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
    AdjointBundle.dependentFiberBundle (I := IG) bundle
  _root_.CovariantDerivative IB EG
    (AdjointBundle.Fiber (I := IG) (torsor := torsor))

variable
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
    {IP : ModelWithCorners ℝ EP HP}
    [IsManifold IB ∞ B]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {bundle : TopologicalPrincipalBundleData torsor}
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

namespace PrincipalConnectionData

/-- Model coordinate of an adjoint section in one fixed designated principal chart. -/
def adjointLocalSectionCoordinate
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor)) : B → EG :=
  fun x =>
    ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart)
      (adjointSection.totalSpace x)).2

/-- Ordinary derivative term in the fixed-chart adjoint-section coordinate. -/
noncomputable def adjointLocalOrdinaryDerivative
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) : EG :=
  let sectionCoordinate := adjointLocalSectionCoordinate
    (IG := IG) (bundle := bundle) chart adjointSection
  NormedSpace.fromTangentSpace (sectionCoordinate b)
    (mfderiv IB (modelWithCornersSelf ℝ EG) sectionCoordinate b X)

/-- Bracket correction `[A(X),σ]` from the exact principal connection and fixed chart. -/
noncomputable def adjointLocalConnectionBracketTerm
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) : EG :=
  let sectionCoordinate := adjointLocalSectionCoordinate
    (IG := IG) (bundle := bundle) chart adjointSection
  let localPotential := connection.pointwise.form.evalOne
    (principalBundleLocalSection chart b)
    (principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b X)
  let coordinates := YangMills.Mathematics.groupLieAlgebraModelEquiv (G := G) IG
  coordinates ⁅localPotential, coordinates.symm (sectionCoordinate b)⁆

/-- The exact designated-chart formula `dσ(X) + [A(X),σ]` in Lie-algebra model coordinates.
The chart is totalized by the existing bundle interface; downstream equalities are required only on
its actual base set. -/
noncomputable def adjointLocalCovariantDerivativeExpression
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) : EG :=
  adjointLocalOrdinaryDerivative (IG := IG) (IB := IB) (bundle := bundle)
      chart adjointSection b X +
    connection.adjointLocalConnectionBracketTerm chart adjointSection b X

/-- The local covariant-derivative expression unfolds to ordinary derivative plus the exact
connection bracket correction. -/
theorem adjointLocalCovariantDerivativeExpression_eq
    (connection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) :
    connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X =
      adjointLocalOrdinaryDerivative (IG := IG) (IB := IB) (bundle := bundle)
        chart adjointSection b X +
      connection.adjointLocalConnectionBracketTerm chart adjointSection b X :=
  rfl

end PrincipalConnectionData

/-- A Mathlib covariant derivative on exact adjoint sections whose value is tied, in every
designated principal chart, to the same principal connection by `d + ad(A)`. -/
structure PrincipalConnectionAdjointCovariantDerivativeData
    (connection : PrincipalConnectionData smoothBundle) where
  /-- Intrinsic covariant derivative obeying Mathlib's additivity and Leibniz laws. -/
  covariantDerivative : AdjointBundle.CovariantDerivative (IG := IG) (IB := IB) bundle
  /-- Exact local formula in every chart of the same designated principal atlas. -/
  coordinate_formula : ∀
    (chart : PrincipalBundleLocalTrivialization torsor),
    chart ∈ bundle.trivializationAtlas →
    ∀ (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor)),
      AdjointBundle.Section.IsSmooth smoothBundle adjointSection →
      ∀ (b : B) (hb : b ∈ chart.baseSet) (X : TangentSpace IB b),
      letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberAddCommGroup (I := IG) bundle b
      letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberModule (I := IG) bundle b
      letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
        AdjointBundle.fiberTopology (I := IG) bundle b
      (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb)
          (covariantDerivative adjointSection b X) =
        connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X

end

end YangMills.Geometry
