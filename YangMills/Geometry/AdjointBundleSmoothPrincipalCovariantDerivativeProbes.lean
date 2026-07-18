/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothPrincipalCovariantDerivative

/-!
# Hostile probes for smooth adjoint covariant derivatives

The probes expose the exact smooth derivative-bundle output, preserve the same-connection local
formula, and reject wrapping a nonsmooth derivative as smooth data.
-/

namespace YangMills.Geometry.AdjointBundleSmoothPrincipalCovariantDerivative.Probes

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

/-- Every exact smooth adjoint section has a smooth total-space section of covariant derivatives. -/
theorem exact_smooth_derivative_output
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (adjointSection : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (section_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection) :
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
    letI : VectorBundle ℝ EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
      AdjointBundle.dependentVectorBundle (I := IG) bundle smoothBundle
    let derivativeTotal : B →
        Bundle.TotalSpace (EB →L[ℝ] EG)
          (fun b => TangentSpace IB b →L[ℝ]
            AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      fun b => ⟨b,
        data.toCovariantDerivativeData.covariantDerivative adjointSection b⟩
    ContMDiff IB (IB.prod (modelWithCornersSelf ℝ (EB →L[ℝ] EG))) ∞
      derivativeTotal :=
  data.smooth_output adjointSection section_smooth

/-- Smooth strengthening preserves the exact same-connection local `d + ad(A)` formula. -/
theorem exact_smooth_data_local_formula
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
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
        (data.toCovariantDerivativeData.covariantDerivative adjointSection b X) =
      connection.adjointLocalCovariantDerivativeExpression chart adjointSection b X :=
  data.toCovariantDerivativeData.coordinate_formula
    chart chart_mem adjointSection section_smooth b hb X

/-- A derivative lacking Mathlib's `C∞` regularity cannot be repackaged as smooth data without
changing the exact underlying same-connection derivative datum. -/
theorem nonsmooth_derivative_wrapper_blocked
    (baseData : PrincipalConnectionAdjointCovariantDerivativeData connection)
    (not_smooth : ¬ AdjointBundle.CovariantDerivative.IsSmooth
      (smoothBundle := smoothBundle) baseData.covariantDerivative) :
    ¬ ∃ smoothData : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection,
      smoothData.toCovariantDerivativeData = baseData := by
  rintro ⟨smoothData, equality⟩
  apply not_smooth
  rw [← equality]
  exact smoothData.smooth

end

end YangMills.Geometry.AdjointBundleSmoothPrincipalCovariantDerivative.Probes
