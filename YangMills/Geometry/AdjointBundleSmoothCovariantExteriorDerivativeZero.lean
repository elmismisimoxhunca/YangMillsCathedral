/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleCovariantExteriorDerivativeZero
import YangMills.Geometry.AdjointBundleSmoothPrincipalCovariantDerivative

/-!
# Smooth degree-zero adjoint covariant exterior differentiation

This module combines the exact degree-zero-to-degree-one packaging with the existing `C∞`
regularity of the same connection-indexed Mathlib covariant derivative. Smoothness is derived by
applying the smooth derivative-bundle section to each locally smooth tangent field and then reading
the resulting adjoint section in the exact designated fiber coordinate.

No new regularity field is introduced. This remains only the degree-zero endpoint of covariant
exterior differentiation; positive degrees and Bianchi are not defined or proved.
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
    {smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle}

/-- A smooth degree-zero adjoint-valued form is sent to the exact smooth degree-one form obtained
from the same connection-indexed covariant derivative. -/
def SmoothPrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero
    {connection : PrincipalConnectionData smoothBundle}
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0) :
    AdjointBundle.DifferentialForm.Smooth smoothBundle 1 where
  toForm := data.toCovariantDerivativeData.covariantExteriorDerivativeZero form.toForm
  smooth := by
    let adjointSection := AdjointBundle.DifferentialForm.toSection form.toForm
    have adjointSection_smooth : AdjointBundle.Section.IsSmooth smoothBundle adjointSection := by
      apply (AdjointBundle.DifferentialForm.isSmooth_ofSection_iff
        smoothBundle adjointSection).mp
      simpa [adjointSection] using form.smooth
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
    letI : ContMDiffVectorBundle ∞ EG
        (AdjointBundle.Fiber (I := IG) (torsor := torsor)) IB :=
      AdjointBundle.dependentContMDiffVectorBundle smoothBundle
    intro chart chart_mem s fields hs fields_smooth
    have derivative_smooth := data.smooth_output adjointSection adjointSection_smooth
    have value_smooth : ContMDiffOn IB (IB.prod 𝓘(ℝ, EG)) ∞
        (fun b => (⟨b, data.toCovariantDerivativeData.covariantDerivative adjointSection b
          (fields 0 b)⟩ : Bundle.TotalSpace EG
            (AdjointBundle.Fiber (I := IG) (torsor := torsor)))) s :=
      derivative_smooth.contMDiffOn.clm_bundle_apply (fields_smooth 0)
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
    letI : MemTrivializationAtlas e := ⟨⟨chart, chart_mem, rfl⟩⟩
    have coordinate_smooth : ContMDiffOn IB 𝓘(ℝ, EG) ∞
        (fun b => (e ⟨b, data.toCovariantDerivativeData.covariantDerivative adjointSection b
          (fields 0 b)⟩).2) s := by
      intro b hb
      exact (e.contMDiffWithinAt_section s (hs hb)).mp (value_smooth b hb)
    exact coordinate_smooth.congr (fun _ _ => rfl)

/-- Forgetting smoothness recovers exactly the previously defined pointwise packaging. -/
@[simp]
theorem SmoothPrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_toForm
    {connection : PrincipalConnectionData smoothBundle}
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0) :
    (data.covariantExteriorDerivativeZero form).toForm =
      data.toCovariantDerivativeData.covariantExteriorDerivativeZero form.toForm :=
  rfl

/-- Evaluation of the smooth packaging remains exactly the original intrinsic derivative. -/
@[simp]
theorem SmoothPrincipalConnectionAdjointCovariantDerivativeData.covariantExteriorDerivativeZero_apply
    {connection : PrincipalConnectionData smoothBundle}
    (data : SmoothPrincipalConnectionAdjointCovariantDerivativeData connection)
    (form : AdjointBundle.DifferentialForm.Smooth smoothBundle 0)
    (b : B) (v : Fin 1 → TangentSpace IB b) :
    ((data.covariantExteriorDerivativeZero form).toForm b) v =
      data.toCovariantDerivativeData.covariantDerivative
        (AdjointBundle.DifferentialForm.toSection form.toForm) b (v 0) := by
  rfl

end

end YangMills.Geometry
