/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleDegreeZeroForm

/-!
# Hostile probes for the degree-zero form/section bridge
-/

namespace YangMills.Geometry.Probes

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
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

omit [IsManifold IB ∞ B] in
/-- A section cannot change after conversion to a degree-zero form and back. -/
theorem disconnected_adjointBundle_sectionDegreeZeroRoundTrip_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (mismatch :
      AdjointBundle.DifferentialForm.toSection (IB := IB) (bundle := bundle)
        (AdjointBundle.DifferentialForm.ofSection (IB := IB) (bundle := bundle) s) ≠ s) : False :=
  mismatch (AdjointBundle.DifferentialForm.toSection_ofSection s)

omit [IsManifold IB ∞ B] in
/-- A degree-zero form cannot change after conversion to a section and back. -/
theorem disconnected_adjointBundle_degreeZeroSectionRoundTrip_blocked
    (form : AdjointBundle.DifferentialForm (IG := IG) (IB := IB) bundle 0)
    (mismatch :
      AdjointBundle.DifferentialForm.ofSection (IB := IB) (bundle := bundle)
        (AdjointBundle.DifferentialForm.toSection form) ≠ form) : False :=
  mismatch (AdjointBundle.DifferentialForm.ofSection_toSection form)

/-- A smooth degree-zero section form cannot have a nonsmooth underlying section. -/
theorem smoothForm_nonsmoothSection_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (formSmooth : AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (AdjointBundle.DifferentialForm.ofSection (IB := IB) (bundle := bundle) s))
    (sectionNonsmooth : ¬AdjointBundle.Section.IsSmooth smoothBundle s) : False :=
  sectionNonsmooth
    ((AdjointBundle.DifferentialForm.isSmooth_ofSection_iff smoothBundle s).mp formSmooth)

/-- A smooth section cannot yield a nonsmooth exact degree-zero form. -/
theorem smoothSection_nonsmoothForm_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (sectionSmooth : AdjointBundle.Section.IsSmooth smoothBundle s)
    (formNonsmooth : ¬AdjointBundle.DifferentialForm.IsSmooth smoothBundle
      (AdjointBundle.DifferentialForm.ofSection (IB := IB) (bundle := bundle) s)) : False :=
  formNonsmooth
    ((AdjointBundle.DifferentialForm.isSmooth_ofSection_iff smoothBundle s).mpr sectionSmooth)

omit [IsManifold IB ∞ B] in
/-- Coordinate evaluation of a degree-zero section form cannot be replaced on a designated chart. -/
theorem replacement_adjointBundle_degreeZeroCoordinate_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (chart : PrincipalBundleLocalTrivialization torsor)
    (fields : Fin 0 → (x : B) → TangentSpace IB x)
    {b : B} (hb : b ∈ chart.baseSet)
    (mismatch :
      AdjointBundle.DifferentialForm.coordinateEvaluation
          (AdjointBundle.DifferentialForm.ofSection (IB := IB) (bundle := bundle) s)
          chart fields b ≠
        ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle chart)
          (s.totalSpace b)).2) : False :=
  mismatch
    (AdjointBundle.DifferentialForm.coordinateEvaluation_ofSection s chart fields hb)

end

end YangMills.Geometry.Probes
