/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundlePrincipalCovariantDerivative

/-!
# Hostile probes for principal-connection adjoint covariant derivatives

The probes expose Mathlib's intrinsic additivity/Leibniz laws and the exact `d + ad(A)` formula in
every designated principal chart. They reject a coordinate value disconnected from the same
principal connection.
-/

namespace YangMills.Geometry.AdjointBundlePrincipalCovariantDerivative.Probes

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
    {connection : PrincipalConnectionData smoothBundle}

/-- The selected derivative is a genuine Mathlib covariant derivative, so additivity and the
section Leibniz rule are not disconnected custom fields. -/
theorem exact_mathlib_covariant_derivative_laws
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection) :
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
    IsCovariantDerivativeOn EG data.covariantDerivative Set.univ := by
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
  exact data.covariantDerivative.isCovariantDerivativeOn

/-- The named local expression unfolds with an explicit plus sign and the exact connection bracket
term. -/
theorem exact_unfolded_d_add_ad_expression
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b) :
    connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X =
      PrincipalConnectionData.adjointLocalOrdinaryDerivative
        (IG := IG) (IB := IB) (bundle := bundle) chart adjointSection b X +
      connection.adjointLocalConnectionBracketTerm chart adjointSection b X :=
  connection.adjointLocalCovariantDerivativeExpression_eq chart adjointSection b X

/-- Omitting a genuinely nonzero connection-bracket term changes the local expression. -/
theorem omitted_connection_bracket_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (b : B) (X : TangentSpace IB b)
    (bracket_nonzero :
      connection.adjointLocalConnectionBracketTerm chart adjointSection b X ≠ 0) :
    PrincipalConnectionData.adjointLocalOrdinaryDerivative
        (IG := IG) (IB := IB) (bundle := bundle) chart adjointSection b X ≠
      connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X := by
  rw [connection.adjointLocalCovariantDerivativeExpression_eq]
  intro equality
  apply bracket_nonzero
  exact add_left_cancel (a := PrincipalConnectionData.adjointLocalOrdinaryDerivative
    (IG := IG) (IB := IB) (bundle := bundle) chart adjointSection b X)
    (by simpa using equality.symm)

/-- Every designated chart exposes the exact local connection formula. -/
theorem exact_local_d_add_ad_formula
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (section_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection)
    (b : B) (hb : b ∈ chart.baseSet) (X : TangentSpace IB b) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb)
        (data.covariantDerivative adjointSection b X) =
      connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X :=
  data.coordinate_formula chart chart_mem adjointSection section_smooth b hb X

/-- A second connection whose local expression differs cannot be substituted into this
connection-indexed derivative datum. -/
theorem unrelated_connection_substitution_blocked
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (otherConnection : PrincipalConnectionData smoothBundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (section_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection)
    (b : B) (hb : b ∈ chart.baseSet) (X : TangentSpace IB b)
    (mismatch :
      otherConnection.adjointLocalCovariantDerivativeExpression chart adjointSection b X ≠
        connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb)
        (data.covariantDerivative adjointSection b X) ≠
      otherConnection.adjointLocalCovariantDerivativeExpression chart adjointSection b X := by
  rw [data.coordinate_formula chart chart_mem adjointSection section_smooth b hb X]
  exact mismatch.symm

/-- A coordinate value that differs from `dσ(X) + [A(X),σ]` cannot replace the selected derivative. -/
theorem disconnected_local_derivative_blocked
    (data : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (section_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection)
    (b : B) (hb : b ∈ chart.baseSet) (X : TangentSpace IB b)
    (replacement : EG)
    (mismatch : replacement ≠
      connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    replacement ≠
      (AdjointBundle.fiberModelContinuousLinearEquiv (IG := IG) bundle chart hb)
        (data.covariantDerivative adjointSection b X) := by
  rw [data.coordinate_formula chart chart_mem adjointSection section_smooth b hb X]
  exact mismatch

end

end YangMills.Geometry.AdjointBundlePrincipalCovariantDerivative.Probes
