/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleLocalTangentLiftSmooth

/-!
# Hostile probes for smooth principal local tangent lifts
-/

namespace YangMills.Geometry.Probes

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
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The derivative-based lift cannot be replaced by a different tangent-map-within value. -/
theorem replacement_localTangentLift_tangentMapWithin_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    {b : B} (hb : b ∈ chart.baseSet) (v : TangentSpace IB b)
    (mismatch :
      (⟨principalBundleLocalSection chart b,
        principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b v⟩ :
          TangentBundle IP P) ≠
        tangentMapWithin IB IP (principalBundleLocalSection chart) chart.baseSet
          ⟨b, v⟩) : False :=
  mismatch (principalBundleLocalTangentLift_eq_tangentMapWithin chart hb v)

/-- A smooth base tangent field cannot acquire a nonsmooth exact local lift. -/
theorem nonsmooth_principalBundle_localLiftedField_blocked
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set B} (hs : s ⊆ chart.baseSet)
    (field : (b : B) → TangentSpace IB b)
    (field_smooth : ContMDiffOn IB IB.tangent ∞
      (fun b => (⟨b, field b⟩ : TangentBundle IB B)) s)
    (failure : ¬ContMDiffOn IB IP.tangent ∞
      (fun b => (⟨principalBundleLocalSection chart b,
        principalBundleLocalTangentLift (IB := IB) (IP := IP)
          chart b (field b)⟩ : TangentBundle IP P)) s) : False :=
  failure (principalBundleLocalTangentLift_contMDiffOn smoothBundle chart chart_mem
    hs field field_smooth)

omit [IsTopologicalGroup G] [IsManifold IB ∞ B] [IsManifold IP ∞ P] in
/-- The tangent-bundle base of a local lift cannot move away from the exact local section. -/
theorem base_moving_principalBundle_localLiftedVector_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (b : B) (v : TangentSpace IB b)
    (mismatch :
      (⟨principalBundleLocalSection chart b,
        principalBundleLocalTangentLift (IB := IB) (IP := IP) chart b v⟩ :
          TangentBundle IP P).proj ≠ principalBundleLocalSection chart b) : False :=
  mismatch (principalBundleLocalTangentLift_totalSpace_proj chart b v)

end

end YangMills.Geometry.Probes
