/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSection
import YangMills.Geometry.AdjointBundleSmoothDifferentialForm

/-!
# Degree-zero adjoint-valued forms and sections

Degree-zero adjoint-bundle-valued forms are identified exactly with dependent adjoint sections. The
local field-evaluation smoothness predicate is proved equivalent to smoothness of the corresponding
section in the named smooth vector-bundle atlas. This supplies an independent coherence bridge; it
does not construct a nonzero field.
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

/-- Regard a dependent adjoint section as a degree-zero varying-fiber form. -/
def ofSection (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) :
    AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0 :=
  fun b => by
    letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberAddCommGroup (I := IG) bundle b
    letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberModule (I := IG) bundle b
    letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
      AdjointBundle.fiberTopology (I := IG) bundle b
    exact ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentSpace IB b) (Fin 0) (s b)

/-- Evaluate a degree-zero varying-fiber form to obtain its dependent adjoint section. -/
def toSection
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0) :
    AdjointBundle.Section (IG := IG) (torsor := torsor) :=
  fun b => (form b) (fun i => Fin.elim0 i)

omit [IsManifold IB ∞ B] in
/-- Evaluating the degree-zero form of a section recovers that section exactly. -/
@[simp]
theorem toSection_ofSection
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) :
    toSection (IB := IB) (bundle := bundle) (ofSection (IB := IB) (bundle := bundle) s) = s := by
  funext b
  rfl

omit [IsManifold IB ∞ B] in
/-- Repackaging the section of a degree-zero form recovers that form exactly. -/
@[simp]
theorem ofSection_toSection
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0) :
    ofSection (IB := IB) (bundle := bundle) (toSection form) = form := by
  funext b
  letI : AddCommGroup (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberAddCommGroup (I := IG) bundle b
  letI : Module ℝ (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberModule (I := IG) bundle b
  letI : TopologicalSpace (AdjointBundle.Fiber (I := IG) (torsor := torsor) b) :=
    AdjointBundle.fiberTopology (I := IG) bundle b
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  rw [hv]
  rfl

omit [IsManifold IB ∞ B] in
/-- Coordinate evaluation of a section regarded as a degree-zero form is exactly the transported
coordinate of that section. -/
theorem coordinateEvaluation_ofSection
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (chart : PrincipalBundleLocalTrivialization torsor)
    (fields : Fin 0 → (x : B) → TangentSpace IB x)
    {b : B} (hb : b ∈ chart.baseSet) :
    coordinateEvaluation (ofSection (IB := IB) (bundle := bundle) s) chart fields b =
      ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart)
        (s.totalSpace b)).2 := by
  rw [coordinateEvaluation_eq_inCoordinates _ chart fields hb,
    inCoordinates_apply]
  rfl

/-- Smoothness of degree-zero forms is exactly smoothness of their corresponding dependent
sections. -/
theorem isSmooth_ofSection_iff
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) :
    IsSmooth smoothBundle (ofSection (IB := IB) (bundle := bundle) s) ↔
      AdjointBundle.Section.IsSmooth smoothBundle s := by
  constructor
  · intro hs
    apply (AdjointBundle.Section.isSmooth_iff_selectedCoordinate smoothBundle s).mpr
    intro b
    let chart := bundle.trivializationAt b
    let fields : Fin 0 → (x : B) → TangentSpace IB x := fun i => Fin.elim0 i
    have coordinateSmooth := hs chart (bundle.trivializationAt_mem_atlas b)
      chart.baseSet fields subset_rfl (fun i => Fin.elim0 i)
    have sectionCoordinateSmooth : ContMDiffOn IB 𝓘(ℝ, EG) ∞
        (fun x =>
          ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart)
            (s.totalSpace x)).2) chart.baseSet :=
      coordinateSmooth.congr fun x hx =>
        coordinateEvaluation_ofSection s chart fields hx
    exact sectionCoordinateSmooth.contMDiffAt
      (chart.isOpen_baseSet.mem_nhds (bundle.mem_baseSet_trivializationAt b))
  · intro hs chart chart_mem t fields ht fields_smooth
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
    let e := AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart
    letI : MemTrivializationAtlas e := ⟨⟨chart, chart_mem, rfl⟩⟩
    change ContMDiff IB (IB.prod 𝓘(ℝ, EG)) ∞ s.totalSpace at hs
    have coordinateSmooth :=
      (e.contMDiffOn_section_baseSet_iff).mp hs.contMDiffOn
    have restricted := coordinateSmooth.mono ht
    refine restricted.congr ?_
    intro b hb
    exact (coordinateEvaluation_ofSection s chart fields (ht hb)).symm

end AdjointBundle.DifferentialForm

end

end YangMills.Geometry
