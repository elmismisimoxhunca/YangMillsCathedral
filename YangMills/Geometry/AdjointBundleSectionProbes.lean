/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.AdjointBundleSection

/-!
# Hostile probes for dependent adjoint-bundle sections
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

/-- A section's total-space realization cannot move its base point. -/
theorem base_moving_adjointBundle_section_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor)) (b : B)
    (mismatch : (s.totalSpace b).proj ≠ b) : False :=
  mismatch (AdjointBundle.Section.totalSpace_proj s b)

/-- Smoothness cannot be disconnected from the selected exact local coordinate at any base point. -/
theorem nonsmooth_adjointBundle_selectedSectionCoordinate_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (hs : AdjointBundle.Section.IsSmooth smoothBundle s) (b : B)
    (failure :
      ¬ContMDiffAt IB 𝓘(ℝ, EG) ∞
        (fun x : B =>
          ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle
            (bundle.trivializationAt b)) (s.totalSpace x)).2) b) : False :=
  failure ((AdjointBundle.Section.isSmooth_iff_selectedCoordinate smoothBundle s).mp hs b)

/-- Smooth selected coordinates at every base point cannot be disconnected from global section
smoothness in the named atlas. -/
theorem disconnected_adjointBundle_selectedSectionCoordinates_blocked
    (s : AdjointBundle.Section (IG := IG) (torsor := torsor))
    (coordinates : ∀ b : B,
      ContMDiffAt IB 𝓘(ℝ, EG) ∞
        (fun x : B =>
          ((AdjointBundle.dependentModelBundleTrivialization (I := IG) bundle
            (bundle.trivializationAt b)) (s.totalSpace x)).2) b)
    (failure : ¬AdjointBundle.Section.IsSmooth smoothBundle s) : False :=
  failure
    ((AdjointBundle.Section.isSmooth_iff_selectedCoordinate smoothBundle s).mpr coordinates)

/-- The consistency zero section cannot be declared nonsmooth for the named smooth bundle. -/
theorem nonsmooth_adjointBundle_zeroSection_blocked
    (failure :
      ¬AdjointBundle.Section.IsSmooth smoothBundle
        (AdjointBundle.Section.zero (IG := IG) bundle)) : False :=
  failure (AdjointBundle.Section.zero_isSmooth smoothBundle)

end

end YangMills.Geometry.Probes
