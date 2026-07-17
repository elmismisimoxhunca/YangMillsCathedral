/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleChartedSpace
import Mathlib.Geometry.Manifold.VectorBundle.FiberwiseLinear

/-!
# Smooth fiberwise-linear atlas on the adjoint quotient

The named charted-space atlas on the existing adjoint orbit quotient is shown compatible with
Mathlib's `contMDiffFiberwiseLinear` structure groupoid. Compatibility is derived pairwise from the
exact quotient transition, exact overlap source, and smooth forward/inverse transition-equivalence
families.

No global charted-space or groupoid instance is installed. No `FiberBundle` or `VectorBundle` is
claimed.
-/

namespace YangMills.Geometry

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

set_option backward.isDefEq.respectTransparency false in
/-- Pairwise compatibility of the named quotient charts with the smooth fiberwise-linear groupoid. -/
@[reducible]
def AdjointBundle.productHasGroupoid :
    @HasGroupoid (B × EG) _ (AdjointBundle (I := IG) torsor) _
      (AdjointBundle.productChartedSpace (IG := IG) bundle)
      (contMDiffFiberwiseLinear B EG IB ∞) := by
  letI : ChartedSpace (B × EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.productChartedSpace (IG := IG) bundle
  refine { compatible := ?_ }
  intro e e' he he'
  rw [AdjointBundle.mem_productChartedSpace_atlas_iff (IG := IG) bundle] at he he'
  obtain ⟨first, first_mem, rfl⟩ := he
  obtain ⟨second, second_mem, rfl⟩ := he'
  rw [mem_contMDiffFiberwiseLinear_iff]
  let φ : B → EG ≃L[ℝ] EG := adjointBundleTransitionEquiv (IG := IG) first second
  let U : Set B := first.baseSet ∩ second.baseSet
  have hU : IsOpen U := first.isOpen_baseSet.inter second.isOpen_baseSet
  have hφ : ContMDiffOn IB 𝓘(ℝ, EG →L[ℝ] EG) ∞
      (fun b => (φ b).toContinuousLinearMap) U :=
    adjointBundleTransitionEquiv_contMDiffOn
      smoothBundle first second first_mem second_mem
  have hφinv : ContMDiffOn IB 𝓘(ℝ, EG →L[ℝ] EG) ∞
      (fun b => (φ b).symm.toContinuousLinearMap) U :=
    adjointBundleTransitionEquiv_symm_contMDiffOn
      smoothBundle first second first_mem second_mem
  refine ⟨φ, U, hU, hφ, hφinv, ?_⟩
  let e₁ := AdjointBundle.modelBundleTrivialization (I := IG) bundle first
  let e₂ := AdjointBundle.modelBundleTrivialization (I := IG) bundle second
  let transition := e₁.toOpenPartialHomeomorph.symm ≫ₕ e₂.toOpenPartialHomeomorph
  let fiberwise := FiberwiseLinear.openPartialHomeomorph φ hU hφ.continuousOn hφinv.continuousOn
  refine ⟨?_, ?_⟩
  · change transition.source = fiberwise.source
    rw [show transition.source = e₁.target ∩ e₁.toOpenPartialHomeomorph.symm ⁻¹' e₂.source by
      exact OpenPartialHomeomorph.trans_source _ _]
    change e₁.target ∩ e₁.toOpenPartialHomeomorph.symm ⁻¹' e₂.source = U ×ˢ Set.univ
    ext z
    constructor
    · rintro ⟨hz₁, hz₂⟩
      have hfirst : z.1 ∈ first.baseSet := e₁.mem_target.mp hz₁
      have hsecondAtInverse : AdjointBundle.projection torsor (e₁.toOpenPartialHomeomorph.symm z) ∈
          second.baseSet := e₂.mem_source.mp hz₂
      have projectionInverse := e₁.proj_symm_apply hz₁
      rw [projectionInverse] at hsecondAtInverse
      exact ⟨⟨hfirst, hsecondAtInverse⟩, Set.mem_univ _⟩
    · rintro ⟨⟨hfirst, hsecond⟩, -⟩
      have hz₁ : z ∈ e₁.target := e₁.mem_target.mpr hfirst
      have hz₂ : e₁.toOpenPartialHomeomorph.symm z ∈ e₂.source := by
        apply e₂.mem_source.mpr
        rw [e₁.proj_symm_apply hz₁]
        exact hsecond
      exact ⟨hz₁, hz₂⟩
  · intro z hz
    change transition z = fiberwise z
    have hz' : z ∈ e₁.target ∩ e₁.toOpenPartialHomeomorph.symm ⁻¹' e₂.source := by
      change z ∈ transition.source at hz
      rw [OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] at hz
      exact hz
    have hfirst : z.1 ∈ first.baseSet := e₁.mem_target.mp hz'.1
    have hsecondAtInverse : AdjointBundle.projection torsor (e₁.toOpenPartialHomeomorph.symm z) ∈
        second.baseSet := e₂.mem_source.mp hz'.2
    have projectionInverse := e₁.proj_symm_apply hz'.1
    rw [projectionInverse] at hsecondAtInverse
    have hdomain : z ∈ (adjointBundleOverlapDomain (I := IG) first second : Set (B × EG)) := by
      rw [adjointBundleOverlapDomain_eq (I := IG) first second]
      exact ⟨⟨hfirst, hsecondAtInverse⟩, Set.mem_univ _⟩
    have transitionEq := adjointBundleModelTransition_eq
      (bundle := bundle) first second z hdomain
    simpa [transition, fiberwise, e₁, e₂, φ,
      adjointBundleTransitionEquiv, FiberwiseLinear.openPartialHomeomorph,
      Function.comp_def] using transitionEq

/-- Named smooth manifold structure on the existing adjoint quotient, obtained by composing the
fiberwise-linear product atlas with the base manifold groupoid. This is not installed globally. -/
@[reducible]
def AdjointBundle.modelIsManifold :
    @IsManifold ℝ _ (EB × EG) _ _ (ModelProd HB EG) _
      (IB.prod 𝓘(ℝ, EG)) ∞ (AdjointBundle (I := IG) torsor) _
      (AdjointBundle.modelChartedSpace (IG := IG) bundle) := by
  letI : ChartedSpace (B × EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.productChartedSpace (IG := IG) bundle
  letI : HasGroupoid (AdjointBundle (I := IG) torsor)
      (contMDiffFiberwiseLinear B EG IB ∞) :=
    AdjointBundle.productHasGroupoid smoothBundle
  letI : ChartedSpace (ModelProd HB EG) (AdjointBundle (I := IG) torsor) :=
    AdjointBundle.modelChartedSpace (IG := IG) bundle
  refine { StructureGroupoid.HasGroupoid.comp
    (contMDiffFiberwiseLinear B EG IB ∞) ?_ with }
  intro e he
  rw [mem_contMDiffFiberwiseLinear_iff] at he
  obtain ⟨φ, U, hU, hφ, h2φ, heφ⟩ := he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  refine ⟨ContMDiffOn.congr ?_ (OpenPartialHomeomorph.EqOnSource.eqOn heφ),
    ContMDiffOn.congr ?_
      (OpenPartialHomeomorph.EqOnSource.eqOn
        (OpenPartialHomeomorph.EqOnSource.symm' heφ))⟩
  · rw [OpenPartialHomeomorph.EqOnSource.source_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (hφ.comp contMDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply contMDiffOn_snd
  · rw [OpenPartialHomeomorph.EqOnSource.target_eq heφ]
    apply contMDiffOn_fst.prodMk
    exact (h2φ.comp contMDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply contMDiffOn_snd

end

end YangMills.Geometry
