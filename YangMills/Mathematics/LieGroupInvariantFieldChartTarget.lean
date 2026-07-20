/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldChartIdentity

/-!
# Invariant Lie-group fields throughout the identity chart target

On the full target of the identity-centered extended chart, the left- and right-invariant field
coordinates are identified with the corresponding second and first partial derivative fields of
centered chart multiplication. The coordinate pullbacks retain `range I`, while partial derivatives
retain the exact chart-target product. No whole-space replacement is made.
-/

namespace YangMills.Mathematics

open Function Bundle Set ChartedSpace Filter
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]

/-- Exact chart identification of the left-invariant field with the second partial of
identity-centered chart multiplication. -/
theorem mpullbackWithin_mulInvariantVectorField_eq_centeredChartMul_secondPartial
    (X : GroupLieAlgebra I G) (z : E) (hz : z ∈ (extChartAt I (1 : G)).target) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X) z =
      fderivWithin ℝ (fun y : E => c (c.symm z * c.symm y)) (range I) a
        (groupLieAlgebraModelEquiv I X) := by
  dsimp
  let c := extChartAt I (1 : G)
  let a := c (1 : G)
  let L : G → G := fun y => c.symm z * y
  have ha : a ∈ c.target := mem_extChartAt_target (1 : G)
  have hzR : z ∈ range I := extChartAt_target_subset_range (1 : G) hz
  have haR : a ∈ range I := extChartAt_target_subset_range (1 : G) ha
  have hcz : c.symm z ∈ c.source := c.map_target hz
  have hca : c.symm a = (1 : G) := extChartAt_to_inv (1 : G)
  have hsA : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I c.symm
      (range I) a := mdifferentiableWithinAt_extChartAt_symm ha
  have hL : MDifferentiableAt I I L (c.symm a) :=
    (contMDiff_mul_left (I := I) (n := ∞)).mdifferentiableAt (by simp)
  have hk : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I (L ∘ c.symm) (range I) a :=
    hL.mdifferentiableWithinAt.comp (u := Set.univ) a hsA (fun _ _ => Set.mem_univ _)
  have hck : (L ∘ c.symm) a = c.symm z := by simp [L, hca]
  have hc : MDifferentiableAt I (modelWithCornersSelf ℝ E) c ((L ∘ c.symm) a) := by
    rw [hck]
    rw [extChartAt_source] at hcz
    exact mdifferentiableAt_extChartAt hcz
  have hu : UniqueMDiffWithinAt (modelWithCornersSelf ℝ E) (range I) a :=
    (I.uniqueDiffOn a haR).uniqueMDiffWithinAt
  have hchain2 := hL.hasMFDerivAt.comp_hasMFDerivWithinAt a
    hsA.hasMFDerivWithinAt
  have hchain1 := hc.hasMFDerivAt.comp_hasMFDerivWithinAt a hchain2
  have hderiv := hchain1.mfderivWithin hu
  have happ := congrArg (fun D : E →L[ℝ] E =>
    D (groupLieAlgebraModelEquiv I X)) hderiv
  let A := mfderivWithin (modelWithCornersSelf ℝ E) I c.symm (range I) z
  have hA : A.IsInvertible := isInvertible_mfderivWithin_extChartAt_symm hz
  let u : E :=
    (mfderivWithin (modelWithCornersSelf ℝ E) I c.symm (range I) a)
      (groupLieAlgebraModelEquiv I X)
  let w : E := (mfderiv I I L (c.symm a)) u
  let v : E := (mfderiv I (modelWithCornersSelf ℝ E) c ((L ∘ c.symm) a)) w
  have happ' :
      (mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
        (c ∘ L ∘ c.symm) (range I) a) (groupLieAlgebraModelEquiv I X) = v := by
    exact happ
  have hcenter : u = groupLieAlgebraModelEquiv I X := by
    dsimp only [u]
    rw [hca]
    change (mfderivWithin (modelWithCornersSelf ℝ E) I
      (extChartAt I (1 : G)).symm (range I) ((extChartAt I (1 : G)) 1)) X = X
    rw [mfderivWithin_range_extChartAt_symm]
    rfl
  have hleft : w = mulInvariantVectorField X (c.symm z) := by
    dsimp only [w]
    rw [hcenter]
    change (mfderiv I I L (c.symm a)) X = _
    rw [hca]
    rfl
  have hv : v = (mfderiv I (modelWithCornersSelf ℝ E) c (c.symm z))
      (mulInvariantVectorField X (c.symm z)) := by
    dsimp only [v]
    rw [hleft]
    rw [hck]
  have hcancel :
      A ((mfderiv I (modelWithCornersSelf ℝ E) c (c.symm z))
        (mulInvariantVectorField X (c.symm z))) =
        mulInvariantVectorField X (c.symm z) := by
    change ((A.comp (mfderiv I (modelWithCornersSelf ℝ E) c (c.symm z)))
      (mulInvariantVectorField X (c.symm z))) = _
    rw [mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz]
    rfl
  change A.inverse (mulInvariantVectorField X (c.symm z)) = _
  rw [hA.inverse_apply_eq]
  rw [← mfderivWithin_eq_fderivWithin]
  change _ = A ((mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E)
    (c ∘ L ∘ c.symm) (range I) a) (groupLieAlgebraModelEquiv I X))
  exact hcancel.symm |>.trans ((congrArg A hv.symm).trans (congrArg A happ'.symm))

set_option backward.isDefEq.respectTransparency true in
/-- On the full identity-chart target, the left-invariant coordinate field is the second partial
of centered chart multiplication on the exact product target. -/
theorem extChartCoordinateField_mulInvariantVectorField_eq_secondPartial_target
    (X : GroupLieAlgebra I G) (z : E)
    (hz : z ∈ (extChartAt I (1 : G)).target) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let t := c.target
    let F := fun p : E × E => c (c.symm p.1 * c.symm p.2)
    extChartCoordinateField I (1 : G) (mulInvariantVectorField X) z =
      fderivWithin ℝ F (t ×ˢ t) (z, a)
        (0, mfderiv I (modelWithCornersSelf ℝ E) c 1 X) := by
  simp only
  let c := extChartAt I (1 : G)
  let a := c (1 : G)
  let t : Set E := c.target
  let F : E × E → E := fun p => c (c.symm p.1 * c.symm p.2)
  let Fc : E × E → E := (c : G → E) ∘ (fun p : G × G => p.1 * p.2) ∘
    (fun p : E × E => (c.symm p.1, c.symm p.2))
  let Xc : E := mfderiv I (modelWithCornersSelf ℝ E) c 1 X
  change extChartCoordinateField I (1 : G) (mulInvariantVectorField X) z =
    fderivWithin ℝ F (t ×ˢ t) (z, a) (0, Xc)
  have ha : a ∈ t := by
    dsimp [a, t, c]
    exact mem_extChartAt_target (1 : G)
  have ht : UniqueDiffOn ℝ t := by
    simpa [t, c] using
      (uniqueMDiffOn_univ.uniqueDiffOn_target_inter (I := I) (1 : G))
  have hca : c.symm a = (1 : G) := by simp [a, c]
  have hcz : c.symm z ∈ c.source := c.map_target hz
  have hsA : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I c.symm
      (range I) a := mdifferentiableWithinAt_extChartAt_symm ha
  let L : G → G := fun y => c.symm z * y
  have hL : MDifferentiableAt I I L (c.symm a) :=
    (contMDiff_mul_left (I := I) (n := ∞)).mdifferentiableAt (by simp)
  have hk : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I
      (L ∘ c.symm) (range I) a :=
    hL.mdifferentiableWithinAt.comp (u := Set.univ) a hsA
      (fun _ _ => Set.mem_univ _)
  have hck : (L ∘ c.symm) a = c.symm z := by simp [L, hca]
  have hc : MDifferentiableAt I (modelWithCornersSelf ℝ E) c ((L ∘ c.symm) a) := by
    rw [hck]
    rw [extChartAt_source] at hcz
    exact mdifferentiableAt_extChartAt hcz
  have hsliceRange : DifferentiableWithinAt ℝ
      (fun y : E => c (c.symm z * c.symm y)) (range I) a := by
    have h := hc.mdifferentiableWithinAt.comp (u := Set.univ) a hk
      (fun _ _ => Set.mem_univ _)
    exact h.differentiableWithinAt
  have hsliceTarget : DifferentiableWithinAt ℝ
      (fun y : E => c (c.symm z * c.symm y)) t a :=
    hsliceRange.mono (extChartAt_target_subset_range (I := I) (1 : G))
  have hrangeTarget :
      fderivWithin ℝ (fun y : E => c (c.symm z * c.symm y)) (range I) a =
        fderivWithin ℝ (fun y : E => c (c.symm z * c.symm y)) t a :=
    fderivWithin_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin (I := I) (1 : G))
      (I.uniqueDiffOn.uniqueDiffWithinAt
        (extChartAt_target_subset_range (I := I) (1 : G) ha)) hsliceTarget
  have hfst : MDifferentiableWithinAt
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ E) Prod.fst (t ×ˢ t) (z, a) :=
    mdifferentiableAt_fst.mdifferentiableWithinAt
  have hsnd : MDifferentiableWithinAt
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E))
      (modelWithCornersSelf ℝ E) Prod.snd (t ×ˢ t) (z, a) :=
    mdifferentiableAt_snd.mdifferentiableWithinAt
  have hsymmZ := (mdifferentiableWithinAt_extChartAt_symm hz).comp (x := (z, a))
    hfst (fun p hp => by
      change p.1 ∈ range I
      exact extChartAt_target_subset_range (I := I) (1 : G) hp.1)
  have hsymmA := (mdifferentiableWithinAt_extChartAt_symm ha).comp (x := (z, a))
    hsnd (fun p hp => by
      change p.2 ∈ range I
      exact extChartAt_target_subset_range (I := I) (1 : G) hp.2)
  have hq := hsymmZ.prodMk hsymmA
  have hq' : MDifferentiableWithinAt
      ((modelWithCornersSelf ℝ E).prod (modelWithCornersSelf ℝ E)) (I.prod I)
      (fun p : E × E => (c.symm p.1, c.symm p.2)) (t ×ˢ t) (z, a) := by
    simpa only [c, Function.comp_apply] using hq
  have hmul : MDifferentiableAt (I.prod I) I (fun p : G × G => p.1 * p.2)
      (c.symm z, c.symm a) :=
    (contMDiff_mul I ∞).mdifferentiableAt (by simp)
  have hprod := hmul.mdifferentiableWithinAt.comp (u := Set.univ) (x := (z, a)) hq'
    (fun _ _ => Set.mem_univ _)
  have hchart : MDifferentiableAt I (modelWithCornersSelf ℝ E) c
      (c.symm z * c.symm a) := by
    rw [hca, mul_one]
    rw [extChartAt_source] at hcz
    exact mdifferentiableAt_extChartAt hcz
  have hF : DifferentiableWithinAt ℝ F (t ×ˢ t) (z, a) := by
    have h := hchart.mdifferentiableWithinAt.comp (u := Set.univ) (x := (z, a)) hprod
      (fun _ _ => Set.mem_univ _)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
    have hFc : Fc = F := by
      funext p
      rfl
    rw [← hFc]
    exact mdifferentiableWithinAt_iff_differentiableWithinAt.mp h
  have hpair : HasFDerivWithinAt (fun y : E => (z, y))
      (ContinuousLinearMap.inr ℝ E E) t a :=
    (by fun_prop : HasFDerivAt (fun y : E => (z, y))
      (ContinuousLinearMap.inr ℝ E E) a).hasFDerivWithinAt
  have hcomp := hF.hasFDerivWithinAt.comp a hpair (fun y hy => ⟨hz, hy⟩)
  have hchain := hcomp.fderivWithin (ht.uniqueDiffWithinAt ha)
  have hXc : Xc = groupLieAlgebraModelEquiv I X := by
    dsimp only [Xc]
    have hx := congrArg (fun D : E →L[ℝ] E => D X)
      (mfderiv_extChartAt_self (I := I) (x := (1 : G)))
    exact hx
  rw [mpullbackWithin_mulInvariantVectorField_eq_centeredChartMul_secondPartial I X z hz]
  rw [hrangeTarget]
  have happ := congrArg (fun D : E →L[ℝ] E => D (groupLieAlgebraModelEquiv I X)) hchain
  change fderivWithin ℝ (fun y : E => F (z, y)) t a
      (groupLieAlgebraModelEquiv I X) = _ at happ
  have harg :
      ((0, Xc) : TangentSpace (modelWithCornersSelf ℝ (E × E)) (z, a)) =
      (0, groupLieAlgebraModelEquiv I X) := by rw [hXc]
  have hargApp := congrArg
    (fun v : E × E => fderivWithin ℝ F (t ×ˢ t) (z, a) v) harg
  have happ' :
      fderivWithin ℝ (fun y : E => F (z, y)) t a
          (groupLieAlgebraModelEquiv I X) =
        fderivWithin ℝ F (t ×ˢ t) (z, a)
          (0, groupLieAlgebraModelEquiv I X) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] using happ
  exact happ'.trans hargApp.symm

/-- On the full target of the identity-centered extended chart, the coordinate field of the
right-invariant vector field is the first partial of centered chart multiplication.  The coordinate
field retains Mathlib's `range I`, while the partial derivative retains the exact chart target. -/
theorem extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_on_target
    (Y : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F : E × E → E := fun w => c (c.symm w.1 * c.symm w.2)
    ∀ z ∈ c.target,
      extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) z =
        fderivWithin ℝ F (c.target ×ˢ c.target) (a, z)
          (mfderiv I 𝓘(ℝ, E) c 1 Y, 0) := by
  dsimp
  let c := extChartAt I (1 : G)
  let a : E := c (1 : G)
  let t : Set E := c.target
  let F : E × E → E := fun w => c (c.symm w.1 * c.symm w.2)
  intro z hz
  change extChartCoordinateField I (1 : G) (mulRightInvariantVectorField I Y) z =
    fderivWithin ℝ F (t ×ˢ t) (a, z) (mfderiv I 𝓘(ℝ, E) c 1 Y, 0)
  have ha : a ∈ t := by
    dsimp [a, t, c]
    exact mem_extChartAt_target 1
  have ht : UniqueDiffOn ℝ t := by
    simpa [t, c] using
      (uniqueMDiffOn_univ.uniqueDiffOn_target_inter (I := I) (1 : G))
  let g : G := c.symm z
  have hgsource : g ∈ c.source := c.map_target hz
  have hcg : c g = z := c.right_inv hz
  have hone : c.symm a = (1 : G) := by simp [a, c]
  have hsymm_a : MDifferentiableWithinAt 𝓘(ℝ, E) I c.symm t a :=
    (mdifferentiableWithinAt_extChartAt_symm ha).mono
      (extChartAt_target_subset_range (I := I) (1 : G))
  have hsymm_z : MDifferentiableWithinAt 𝓘(ℝ, E) I c.symm t z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mono
      (extChartAt_target_subset_range (I := I) (1 : G))
  have hfst : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
      Prod.fst (t ×ˢ t) (a, z) := mdifferentiableAt_fst.mdifferentiableWithinAt
  have hsnd : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
      Prod.snd (t ×ˢ t) (a, z) := mdifferentiableAt_snd.mdifferentiableWithinAt
  have hsymm_fst : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) I
      (c.symm ∘ Prod.fst) (t ×ˢ t) (a, z) :=
    hsymm_a.comp (a, z) hfst (fun _ hw => hw.1)
  have hsymm_snd : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) I
      (c.symm ∘ Prod.snd) (t ×ˢ t) (a, z) :=
    hsymm_z.comp (a, z) hsnd (fun _ hw => hw.2)
  have hpair : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (I.prod I)
      (fun w : E × E => (c.symm w.1, c.symm w.2)) (t ×ˢ t) (a, z) := by
    simpa only [Function.comp_apply] using hsymm_fst.prodMk hsymm_snd
  have hmul : MDifferentiableAt (I.prod I) I (fun p : G × G => p.1 * p.2)
      ((1 : G), g) := (contMDiff_mul I ∞).mdifferentiableAt (by simp)
  have hmulPair : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) I
      ((fun p : G × G => p.1 * p.2) ∘
        (fun w : E × E => (c.symm w.1, c.symm w.2))) (t ×ˢ t) (a, z) := by
    apply hmul.comp_mdifferentiableWithinAt_of_eq (a, z) hpair
    exact Prod.ext hone rfl
  have hc : MDifferentiableAt I 𝓘(ℝ, E) c g := by
    exact mdifferentiableAt_extChartAt (by simpa [c] using hgsource)
  have hFmd : MDifferentiableWithinAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E)
      F (t ×ˢ t) (a, z) := by
    have h := hc.comp_mdifferentiableWithinAt_of_eq (a, z) hmulPair (by simp [hone, g])
    simpa [F, Function.comp_def] using h
  have hFmd' : MDifferentiableWithinAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      F (t ×ˢ t) (a, z) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hFmd
  have hF : DifferentiableWithinAt ℝ F (t ×ˢ t) (a, z) :=
    hFmd'.differentiableWithinAt
  have hinsert : DifferentiableWithinAt ℝ (fun w : E => (w, z)) t a := by fun_prop
  have hinsertMaps : MapsTo (fun w : E => (w, z)) t (t ×ˢ t) :=
    fun _ hw => ⟨hw, hz⟩
  have hchainInsert := fderivWithin_comp (𝕜 := ℝ) (f := fun w : E => (w, z))
    (g := F) (s := t) (t := t ×ˢ t) a hF hinsert hinsertMaps (ht a ha)
  have hinsertDeriv :
      fderivWithin ℝ (fun w : E => (w, z)) t a = ContinuousLinearMap.inl ℝ E E := by
    have hp := differentiableWithinAt_id.fderivWithin_prodMk
      (differentiableWithinAt_const (c := z)) (ht a ha)
    rw [fderivWithin_id (ht a ha)] at hp
    rw [fderivWithin_const_apply] at hp
    simpa [id_eq, ContinuousLinearMap.inl] using hp
  have hpartial (v : E) :
      fderivWithin ℝ F (t ×ˢ t) (a, z) (v, 0) =
        fderivWithin ℝ (fun w : E => F (w, z)) t a v := by
    have happ := congrArg (fun L : E →L[ℝ] E => L v) hchainInsert
    rw [hinsertDeriv] at happ
    change fderivWithin ℝ (fun w : E => F (w, z)) t a v =
      fderivWithin ℝ F (t ×ˢ t) (a, z) (v, 0) at happ
    exact happ.symm
  have hrightPair : MDifferentiableAt I (I.prod I) (fun q : G => (q, g)) 1 :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hright : MDifferentiableAt I I (fun q : G => q * g) 1 := by
    have h := hmul.comp 1 hrightPair
    simpa [Function.comp_def] using h
  have hrightSymm : MDifferentiableWithinAt 𝓘(ℝ, E) I
      ((fun q : G => q * g) ∘ c.symm) t a :=
    hright.comp_mdifferentiableWithinAt_of_eq a hsymm_a hone
  have hsliceMD : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (c ∘ (fun q : G => q * g) ∘ c.symm) t a :=
    hc.comp_mdifferentiableWithinAt_of_eq a hrightSymm (by simp [hone])
  have hsymmDeriv :
      mfderivWithin 𝓘(ℝ, E) I c.symm t a =
        mfderivWithin 𝓘(ℝ, E) I c.symm (range I) a :=
    (mdifferentiableWithinAt_extChartAt_symm ha).mfderivWithin_mono
      ((ht a ha).uniqueMDiffWithinAt) (extChartAt_target_subset_range (I := I) (1 : G))
  let Yc : E := mfderiv I 𝓘(ℝ, E) c 1 Y
  have hsymmYRange :
      mfderivWithin 𝓘(ℝ, E) I c.symm (range I) a Yc = Y := by
    rw [hone]
    have hcomp := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := I) (x := (1 : G)) (y := (1 : G)) (mem_extChartAt_source (1 : G))
    have happ := congrArg (fun L : TangentSpace I (1 : G) →L[ℝ]
      TangentSpace I (1 : G) => L Y) hcomp
    change mfderivWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (range I)
        ((extChartAt I (1 : G)) 1)
          (mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) 1 Y) = Y at happ
    exact happ
  have hsymmY : mfderivWithin 𝓘(ℝ, E) I c.symm t a Yc = Y := by
    rw [hsymmDeriv]
    exact hsymmYRange
  have hrightChain :
      mfderivWithin 𝓘(ℝ, E) I ((fun q : G => q * g) ∘ c.symm) t a =
        (mfderiv I I (fun q : G => q * g) 1).comp
          (mfderivWithin 𝓘(ℝ, E) I c.symm t a) := by
    exact mfderiv_comp_mfderivWithin_of_eq hright hsymm_a
      ((ht a ha).uniqueMDiffWithinAt) hone
  have hsliceChain :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
          (c ∘ (fun q : G => q * g) ∘ c.symm) t a =
        (mfderiv I 𝓘(ℝ, E) c g).comp
          (mfderivWithin 𝓘(ℝ, E) I ((fun q : G => q * g) ∘ c.symm) t a) := by
    exact mfderiv_comp_mfderivWithin_of_eq hc hrightSymm
      ((ht a ha).uniqueMDiffWithinAt) (by simp [hone])
  have hrightApply :
      mfderivWithin 𝓘(ℝ, E) I ((fun q : G => q * g) ∘ c.symm) t a Yc =
        mfderiv I I (fun q : G => q * g) 1 Y := by
    have happ := congrArg (fun L => L Yc) hrightChain
    change mfderivWithin 𝓘(ℝ, E) I ((fun q : G => q * g) ∘ c.symm) t a Yc =
      mfderiv I I (fun q : G => q * g) 1
        (mfderivWithin 𝓘(ℝ, E) I c.symm t a Yc) at happ
    rw [hsymmY] at happ
    exact happ
  have hsliceApply :
      mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
          (c ∘ (fun q : G => q * g) ∘ c.symm) t a Yc =
        mfderiv I 𝓘(ℝ, E) c g (mulRightInvariantVectorField I Y g) := by
    have happ := congrArg (fun L => L Yc) hsliceChain
    change mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
        (c ∘ (fun q : G => q * g) ∘ c.symm) t a Yc =
      mfderiv I 𝓘(ℝ, E) c g
        (mfderivWithin 𝓘(ℝ, E) I ((fun q : G => q * g) ∘ c.symm) t a Yc) at happ
    rw [hrightApply] at happ
    exact happ
  have hslice :
      fderivWithin ℝ (fun w : E => F (w, z)) t a Yc =
        mfderiv I 𝓘(ℝ, E) c g (mulRightInvariantVectorField I Y g) := by
    have hfun : (fun w : E => F (w, z)) =
        c ∘ (fun q : G => q * g) ∘ c.symm := by
      funext w
      simp only [F, Function.comp_apply, g]
    rw [hfun, ← mfderivWithin_eq_fderivWithin]
    exact hsliceApply
  have hinv :
      (mfderivWithin 𝓘(ℝ, E) I c.symm (range I) z).inverse =
        mfderiv I 𝓘(ℝ, E) c g := by
    have h1 := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
      (I := I) (x := (1 : G)) hz
    have h2 := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
      (I := I) (x := (1 : G)) hz
    simpa only [c, g] using ContinuousLinearMap.inverse_eq h2 h1
  rw [extChartCoordinateField, VectorField.mpullbackWithin_apply]
  change (mfderivWithin 𝓘(ℝ, E) I c.symm (range I) z).inverse
      (mulRightInvariantVectorField I Y g) = _
  rw [hinv, hpartial]
  exact hslice.symm

/-- `EqOn` form used by the intrinsic invariant-field commutation theorem. -/
theorem mpullbackWithin_mulRightInvariantVectorField_eq_firstPartial_on_target
    (Y : GroupLieAlgebra I G) :
    let c := extChartAt I (1 : G)
    let a := c (1 : G)
    let F : E × E → E := fun w => c (c.symm w.1 * c.symm w.2)
    let Yc : E := mfderiv I 𝓘(ℝ, E) c 1 Y
    Set.EqOn
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm
        (mulRightInvariantVectorField I Y) (range I))
      (fun z => fderivWithin ℝ F (c.target ×ˢ c.target) (a, z) (Yc, 0))
      c.target := by
  dsimp
  intro z hz
  exact extChartCoordinateField_mulRightInvariantVectorField_eq_firstPartial_on_target I Y z hz

end

end YangMills.Mathematics
