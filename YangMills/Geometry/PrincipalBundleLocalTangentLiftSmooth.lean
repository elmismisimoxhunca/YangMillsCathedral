/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLift
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smoothness of principal local tangent lifts

The derivative-based tangent lift from a designated local section agrees with Mathlib's tangent map
within the chart domain. Therefore applying it to a smooth base tangent field produces a smooth
tangent field along that exact local section.

This is reusable manifold infrastructure. It does not assert smoothness of descended curvature or
add any pullback-regularity certificate.
-/

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff Bundle

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

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- On the open chart domain, the derivative-based local lift is exactly Mathlib's tangent map
within that domain. -/
theorem principalBundleLocalTangentLift_eq_tangentMapWithin
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet)
    (v : TangentSpace IB b) :
    (⟨principalBundleLocalSection chart b,
      principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b v⟩ :
        TangentBundle IP P) =
      tangentMapWithin IB IP (principalBundleLocalSection chart) chart.baseSet
        ⟨b, v⟩ := by
  change (⟨principalBundleLocalSection chart b,
      mfderiv IB IP (principalBundleLocalSection chart) b v⟩ : TangentBundle IP P) =
    ⟨principalBundleLocalSection chart b,
      mfderivWithin IB IP (principalBundleLocalSection chart) chart.baseSet b v⟩
  rw [mfderivWithin_of_mem_nhds (chart.isOpen_baseSet.mem_nhds hb)]

/-- Applying the exact local tangent lift to a smooth base tangent field gives a smooth tangent field
along the designated local section. -/
theorem principalBundleLocalTangentLift_contMDiffOn
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s) :
    ContMDiffOn IB IP.tangent ∞
      (fun b => (⟨principalBundleLocalSection chart b,
        principalBundleLocalTangentLift (IB := IB) (IP := IP)
          chart b (field b)⟩ : TangentBundle IP P)) s := by
  have tangentSmooth :=
    (principalBundleLocalSection_contMDiffOn smoothBundle chart chart_mem)
      |>.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
        chart.isOpen_baseSet.uniqueMDiffOn
  have maps : Set.MapsTo
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s
      (Bundle.TotalSpace.proj ⁻¹' chart.baseSet) := by
    intro b hb
    exact hs hb
  have composed := tangentSmooth.comp field_smooth maps
  refine composed.congr ?_
  intro b hb
  exact principalBundleLocalTangentLift_eq_tangentMapWithin chart (hs hb) (field b)

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The base point of the lifted tangent field is exactly the designated local section, not an
unrelated point of the principal total space. -/
@[simp]
theorem principalBundleLocalTangentLift_totalSpace_proj
    (chart : PrincipalBundleLocalTrivialization torsor)
    (b : B) (v : TangentSpace IB b) :
    (⟨principalBundleLocalSection chart b,
      principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b v⟩ :
        TangentBundle IP P).proj = principalBundleLocalSection chart b :=
  rfl

end

end YangMills.Geometry
