/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Geometry.Manifold.VectorField.LieBracket
import YangMills.Geometry.SmoothPrincipalBundle

/-!
# Lie-bracket transport through smooth open partial diffeomorphisms

Mathlib's within-bracket pullback naturality is packaged for mutually inverse smooth restrictions of
open partial homeomorphisms, including canonical target-open source restrictions. A downstream
specialization applies this to designated smooth principal trivializations.
-/

open Set Function
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM'

namespace YangMills.Mathematics

variable
    {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    [IsManifold I ∞ M] [IsManifold I' ∞ M']

noncomputable section

private theorem minSmoothness_le_top : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact (show (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from
    WithTop.coe_le_coe.mpr le_top)

/-- Lie brackets commute with pullback through a smooth open restriction of an open partial
homeomorphism. The hypotheses retain both smooth mutually inverse directions and both set maps, as
provided by a smooth principal local trivialization. Mathlib's bracket theorem uses the forward
smoothness and the open source; the inverse hypotheses certify that the chosen open sets really are
a partial-diffeomorphism restriction rather than an unrelated one-way map. -/
theorem OpenPartialHomeomorph.mpullbackWithin_mlieBracketWithin_open
    [CompleteSpace E]
    (e : OpenPartialHomeomorph M M')
    {s : Set M} {t : Set M'}
    (hs : IsOpen s) (_ht : IsOpen t)
    (_hsSource : s ⊆ e.source) (_htTarget : t ⊆ e.target)
    (he : ContMDiffOn I I' ∞ e s)
    (_heInv : ContMDiffOn I' I ∞ e.symm t)
    (hst : MapsTo e s t) (_hts : MapsTo e.symm t s)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hx : x ∈ s)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) t (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) t (e x)) :
    VectorField.mpullbackWithin I I' e
        (VectorField.mlieBracketWithin I' V W t) s x =
      VectorField.mlieBracketWithin I
        (VectorField.mpullbackWithin I I' e V s)
        (VectorField.mpullbackWithin I I' e W s) s x := by
  letI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) minSmoothness_le_top
  letI : IsManifold I' (minSmoothness ℝ 2) M' :=
    IsManifold.of_le (m := minSmoothness ℝ 2) (n := ∞) minSmoothness_le_top
  have hpre : (e : M → M') ⁻¹' t ∈ nhdsWithin x s := by
    apply Filter.mem_of_superset self_mem_nhdsWithin
    exact hst
  have hclosure : x ∈ closure (interior s) := by
    rw [hs.interior_eq]
    exact subset_closure hx
  exact VectorField.mpullbackWithin_mlieBracketWithin
    hV hW hs.uniqueMDiffOn (he x hx) hx minSmoothness_le_top hpre hclosure

/-- Full-domain specialization for a smooth open partial diffeomorphism. -/
theorem OpenPartialHomeomorph.mpullbackWithin_mlieBracketWithin
    [CompleteSpace E]
    (e : OpenPartialHomeomorph M M')
    (he : ContMDiffOn I I' ∞ e e.source)
    (heInv : ContMDiffOn I' I ∞ e.symm e.target)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hx : x ∈ e.source)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) e.target (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) e.target (e x)) :
    VectorField.mpullbackWithin I I' e
        (VectorField.mlieBracketWithin I' V W e.target) e.source x =
      VectorField.mlieBracketWithin I
        (VectorField.mpullbackWithin I I' e V e.source)
        (VectorField.mpullbackWithin I I' e W e.source) e.source x := by
  apply OpenPartialHomeomorph.mpullbackWithin_mlieBracketWithin_open
    e e.open_source e.open_target Subset.rfl Subset.rfl he heInv
      (fun _ hx' => e.map_source hx') (fun _ hy' => e.symm.map_source hy') hx hV hW

/-- A zero target bracket pulls back to a zero bracket on the source open set. This is the form
needed to move a product-coordinate bracket calculation through a principal local trivialization. -/
theorem OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_open
    [CompleteSpace E]
    (e : OpenPartialHomeomorph M M')
    {s : Set M} {t : Set M'}
    (hs : IsOpen s) (ht : IsOpen t)
    (hsSource : s ⊆ e.source) (htTarget : t ⊆ e.target)
    (he : ContMDiffOn I I' ∞ e s)
    (heInv : ContMDiffOn I' I ∞ e.symm t)
    (hst : MapsTo e s t) (hts : MapsTo e.symm t s)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hx : x ∈ s)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) t (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) t (e x))
    (hzero : VectorField.mlieBracketWithin I' V W t (e x) = 0) :
    VectorField.mlieBracketWithin I
        (VectorField.mpullbackWithin I I' e V s)
        (VectorField.mpullbackWithin I I' e W s) s x = 0 := by
  rw [← OpenPartialHomeomorph.mpullbackWithin_mlieBracketWithin_open
    e hs ht hsSource htTarget he heInv hst hts hx hV hW]
  simp only [VectorField.mpullbackWithin_apply, hzero, map_zero]

/-- Canonical target-open restriction. Restricting the source to
`e.source ∩ e ⁻¹' t` automatically provides the matching open set and both set maps. -/
theorem OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_targetOpen
    [CompleteSpace E]
    (e : OpenPartialHomeomorph M M')
    {t : Set M'} (ht : IsOpen t) (htTarget : t ⊆ e.target)
    (he : ContMDiffOn I I' ∞ e e.source)
    (heInv : ContMDiffOn I' I ∞ e.symm e.target)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hxSource : x ∈ e.source) (hxt : e x ∈ t)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) t (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) t (e x))
    (hzero : VectorField.mlieBracketWithin I' V W t (e x) = 0) :
    VectorField.mlieBracketWithin I
        (VectorField.mpullbackWithin I I' e V (e.source ∩ e ⁻¹' t))
        (VectorField.mpullbackWithin I I' e W (e.source ∩ e ⁻¹' t))
        (e.source ∩ e ⁻¹' t) x = 0 := by
  apply OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_open
    e (e.isOpen_inter_preimage ht) ht inter_subset_left htTarget
      (he.mono inter_subset_left) (heInv.mono htTarget)
  · intro y hy
    exact hy.2
  · intro y hy
    refine ⟨e.map_target (htTarget hy), ?_⟩
    change e (e.symm y) ∈ t
    rw [e.right_inv (htTarget hy)]
    exact hy
  · exact ⟨hxSource, hxt⟩
  · exact hV
  · exact hW
  · exact hzero

/-- Full-domain zero-bracket specialization. -/
theorem OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero
    [CompleteSpace E]
    (e : OpenPartialHomeomorph M M')
    (he : ContMDiffOn I I' ∞ e e.source)
    (heInv : ContMDiffOn I' I ∞ e.symm e.target)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hx : x ∈ e.source)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) e.target (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) e.target (e x))
    (hzero : VectorField.mlieBracketWithin I' V W e.target (e x) = 0) :
    VectorField.mlieBracketWithin I
        (VectorField.mpullbackWithin I I' e V e.source)
        (VectorField.mpullbackWithin I I' e W e.source) e.source x = 0 := by
  apply OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_open
    e e.open_source e.open_target Subset.rfl Subset.rfl he heInv
      (fun _ hx' => e.map_source hx') (fun _ hy' => e.symm.map_source hy')
      hx hV hW hzero

end
end YangMills.Mathematics

namespace YangMills.Geometry

open Set
open scoped Manifold ContDiff

universe uEG uHG uEB uHB uEP uHP uG uB uP

variable
    {EG : Type uEG} {HG : Type uHG}
    [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
    {EP : Type uEP} {HP : Type uHP}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [CompleteSpace EP] [TopologicalSpace HP]
    {G : Type uG} {B : Type uB} {P : Type uP}
    [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]
    [IsTopologicalGroup G]
    {IB : ModelWithCorners ℝ EB HB}
    {IG : ModelWithCorners ℝ EG HG}
    {IP : ModelWithCorners ℝ EP HP}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ChartedSpace HG G] [LieGroup IG ∞ G]
    [ChartedSpace HP P] [IsManifold IP ∞ P]
    {torsor : PrincipalBundleTorsorData G B P}
    {bundle : TopologicalPrincipalBundleData torsor}

noncomputable section

/-- Principal-trivialization specialization for a target-open restriction. This is directly
applicable with the intersection of a principal chart target and the natural product-bracket domain;
the matching total-space open set is constructed canonically as its chart preimage. -/
theorem SmoothPrincipalBundleData.mlieBracketWithin_mpullbackWithin_eq_zero_targetOpen
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {t : Set (B × G)} (ht : IsOpen t)
    (htTarget : t ⊆ chart.toPartialHomeomorph.target)
    {V W : (y : B × G) → TangentSpace (IB.prod IG) y} {p : P}
    (hpSource : p ∈ chart.toPartialHomeomorph.source)
    (hpt : chart.toPartialHomeomorph p ∈ t)
    (hV : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle (IB.prod IG) (B × G))) t
      (chart.toPartialHomeomorph p))
    (hW : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun y => (⟨y, W y⟩ : TangentBundle (IB.prod IG) (B × G))) t
      (chart.toPartialHomeomorph p))
    (hzero : VectorField.mlieBracketWithin (IB.prod IG) V W t
      (chart.toPartialHomeomorph p) = 0) :
    VectorField.mlieBracketWithin IP
        (VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph V
          (chart.toPartialHomeomorph.source ∩ chart.toPartialHomeomorph ⁻¹' t))
        (VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph W
          (chart.toPartialHomeomorph.source ∩ chart.toPartialHomeomorph ⁻¹' t))
        (chart.toPartialHomeomorph.source ∩ chart.toPartialHomeomorph ⁻¹' t) p = 0 := by
  apply YangMills.Mathematics.OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_targetOpen
    chart.toPartialHomeomorph ht htTarget
      (smoothBundle.trivialization_smooth chart chart_mem)
      (smoothBundle.inverse_trivialization_smooth chart chart_mem)
      hpSource hpt hV hW hzero

/-- Principal-trivialization specialization: a product-coordinate zero bracket on matching open
sets pulls back to zero on the principal total space. All smoothness is discharged by the exact
forward/inverse atlas fields of `SmoothPrincipalBundleData`. -/
theorem SmoothPrincipalBundleData.mlieBracketWithin_mpullbackWithin_eq_zero_open
    (smoothBundle : SmoothPrincipalBundleData IB IG IP torsor bundle)
    (chart : PrincipalBundleLocalTrivialization torsor)
    (chart_mem : chart ∈ bundle.trivializationAtlas)
    {s : Set P} {t : Set (B × G)}
    (hs : IsOpen s) (ht : IsOpen t)
    (hsSource : s ⊆ chart.toPartialHomeomorph.source)
    (htTarget : t ⊆ chart.toPartialHomeomorph.target)
    (hst : MapsTo chart.toPartialHomeomorph s t)
    (hts : MapsTo chart.toPartialHomeomorph.symm t s)
    {V W : (y : B × G) → TangentSpace (IB.prod IG) y} {p : P}
    (hp : p ∈ s)
    (hV : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle (IB.prod IG) (B × G))) t
      (chart.toPartialHomeomorph p))
    (hW : MDifferentiableWithinAt (IB.prod IG) (IB.prod IG).tangent
      (fun y => (⟨y, W y⟩ : TangentBundle (IB.prod IG) (B × G))) t
      (chart.toPartialHomeomorph p))
    (hzero : VectorField.mlieBracketWithin (IB.prod IG) V W t
      (chart.toPartialHomeomorph p) = 0) :
    VectorField.mlieBracketWithin IP
        (VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph V s)
        (VectorField.mpullbackWithin IP (IB.prod IG) chart.toPartialHomeomorph W s)
        s p = 0 := by
  apply YangMills.Mathematics.OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_open
    chart.toPartialHomeomorph hs ht hsSource htTarget
    ((smoothBundle.trivialization_smooth chart chart_mem).mono hsSource)
    ((smoothBundle.inverse_trivialization_smooth chart chart_mem).mono htTarget)
    hst hts hp hV hW hzero

end
end YangMills.Geometry
