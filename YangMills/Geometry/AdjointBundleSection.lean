/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSmoothVectorBundle

/-!
# Sections of the dependent adjoint bundle

A section chooses one quotient-derived adjoint fiber element over every base point. Smoothness is
defined through Mathlib's smooth-vector-bundle total-space atlas after installing only the named
fiber algebra, preserved quotient-induced topology, and exact transported bundle structures locally.
A local-coordinate criterion and the smooth zero section are derived.

No nonzero section, connection, curvature, or Yang--Mills field is constructed.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle Topology

universe uEG uHG uEB uHB uEP uHP uG uB uP

noncomputable section

/-- A section of the dependent adjoint bundle. -/
def AdjointBundle.Section
    {EG : Type uEG} {HG : Type uHG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    [TopologicalSpace HG]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IG : ModelWithCorners ℝ EG HG} [ChartedSpace HG G] [LieGroup IG ∞ G]
    {torsor : PrincipalBundleTorsorData G B P} :=
  (b : B) → AdjointBundle.Fiber (I := IG) (torsor := torsor) b

namespace AdjointBundle.Section

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

/-- The total-space map underlying a dependent adjoint section. -/
def totalSpace (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) :
    B → Bundle.TotalSpace EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) :=
  fun b => ⟨b, s b⟩

@[simp]
theorem totalSpace_proj (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) (b : B) :
    (s.totalSpace b).proj = b :=
  rfl

@[simp]
theorem totalSpace_snd (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) (b : B) :
    (s.totalSpace b).2 = s b :=
  rfl

/-- The zero section for the named selected-coordinate fiber algebra. -/
def zero (bundle : TopologicalPrincipalBundleData torsor) :
    AdjointBundle.Section (IG := IG) (torsor := torsor) :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    exact 0

@[simp]
theorem zero_apply (bundle : TopologicalPrincipalBundleData torsor) (b : B) :
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    zero (IG := IG) bundle b = 0 :=
  rfl

/-- Smoothness of a section in the exact dependent smooth-vector-bundle atlas. -/
def IsSmooth (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) : Prop :=
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
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
  ContMDiff IB (IB.prod 𝓘(ℝ, EG)) ∞ s.totalSpace

/-- A section is smooth exactly when its coordinate in the designated chart selected at every base
point is smooth at that point. -/
theorem isSmooth_iff_selectedCoordinate
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) :
    IsSmooth smoothBundle s ↔
      ∀ b : B,
        ContMDiffAt IB 𝓘(ℝ, EG) ∞
          (fun x : B =>
            ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle
              (bundle.trivializationAt b)) (s.totalSpace x)).2) b := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
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
  change ContMDiff IB (IB.prod 𝓘(ℝ, EG)) ∞ s.totalSpace ↔ _
  constructor
  · intro hs b
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt b)
    letI : MemTrivializationAtlas e :=
      ⟨⟨bundle.trivializationAt b, bundle.trivializationAt_mem_atlas b, rfl⟩⟩
    exact (e.contMDiffAt_section_iff (bundle.mem_baseSet_trivializationAt b)).mp (hs b)
  · intro hs b
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle
      (bundle.trivializationAt b)
    letI : MemTrivializationAtlas e :=
      ⟨⟨bundle.trivializationAt b, bundle.trivializationAt_mem_atlas b, rfl⟩⟩
    exact (e.contMDiffAt_section_iff (bundle.mem_baseSet_trivializationAt b)).mpr (hs b)

/-- The named zero section is smooth. This is consistency infrastructure, not a nontrivial field
witness. -/
theorem zero_isSmooth
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle) :
    IsSmooth smoothBundle (zero (IG := IG) bundle) := by
  letI (b : B) : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI (b : B) : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI (b : B) : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
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
  change ContMDiff IB (IB.prod 𝓘(ℝ, EG)) ∞
    (zero (IG := IG) bundle).totalSpace
  have zero_totalSpace_eq :
      (zero (IG := IG) bundle).totalSpace =
        Bundle.zeroSection EG (AdjointBundle.Fiber (I := IG) (torsor := torsor)) := by
    funext b
    rfl
  rw [zero_totalSpace_eq]
  exact Bundle.contMDiff_zeroSection ℝ
    (AdjointBundle.Fiber (I := IG) (torsor := torsor))

end AdjointBundle.Section

end

end YangMills.Geometry
