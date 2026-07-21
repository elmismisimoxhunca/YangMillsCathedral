/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalOrbitAdaptedProductField

/-!
# Product bracket of fundamental and orbit-adapted fields

In base/group product coordinates, the vertical fundamental field and the prescribed-value
orbit-adapted field have zero intrinsic within-bracket at the normalized center. The proof retains
the exact open product domain and derives the separated coordinate bracket factorwise.
-/

namespace YangMills.Geometry.PrincipalOrbitAdapted

open Set Function Bundle
open scoped Manifold ContDiff
open YangMills.Mathematics

universe uE uH uG uEB uHB uB

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]
    {EB : Type uEB} {HB : Type uHB}
    [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    [TopologicalSpace HB]
    {B : Type uB} [TopologicalSpace B]
    (IB : ModelWithCorners ℝ EB HB)
    [ChartedSpace HB B] [IsManifold IB ∞ B]

private def verticalFundamentalProductField
    (X : GroupLieAlgebra I G) (z : B × G) : TangentSpace (IB.prod I) z :=
  (0, mulInvariantVectorField X z.2)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ EB] in
private lemma product_mpullback_vertical_apply
    (X : GroupLieAlgebra I G) (b : B) (z : EB × E)
    (hz : z ∈ (extChartAt (IB.prod I) (b, (1 : G))).target) :
    VectorField.mpullbackWithin (modelWithCornersSelf ℝ (EB × E)) (IB.prod I)
      (extChartAt (IB.prod I) (b, (1 : G))).symm
      (verticalFundamentalProductField I IB X) (range (IB.prod I)) z =
    (0, VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
      (extChartAt I (1 : G)).symm (mulInvariantVectorField X) (range I) z.2) := by
  have hzfull := hz
  simp only [VectorField.mpullbackWithin_apply]
  rw [(isInvertible_mfderivWithin_extChartAt_symm hzfull).inverse_apply_eq]
  rw [extChartAt_prod] at hz
  simp only [PartialEquiv.prod_target] at hz
  rw [extChartAt_prod]
  simp only [PartialEquiv.prod_coe_symm, ModelWithCorners.range_prod,
    verticalFundamentalProductField]
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  change (_ = mfderivWithin ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
    (IB.prod I) (Prod.map (extChartAt IB b).symm (extChartAt I (1 : G)).symm)
    (range IB ×ˢ range I) z _)
  rw [mfderivWithin_prodMap
    (mdifferentiableWithinAt_extChartAt_symm hz.1)
    (mdifferentiableWithinAt_extChartAt_symm hz.2)
    (IB.uniqueMDiffOn z.1 (extChartAt_target_subset_range b hz.1))
    (I.uniqueMDiffOn z.2 (extChartAt_target_subset_range 1 hz.2))]
  change (0, mulInvariantVectorField X ((extChartAt I (1 : G)).symm z.2)) =
    (_, mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (1 : G)).symm
      (range I) z.2 ((mfderivWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I (1 : G)).symm (range I) z.2).inverse
          (mulInvariantVectorField X ((extChartAt I (1 : G)).symm z.2))))
  rw [ContinuousLinearMap.IsInvertible.self_apply_inverse
    (isInvertible_mfderivWithin_extChartAt_symm hz.2)]
  apply Prod.ext
  · change (0 : TangentSpace IB ((extChartAt IB b).symm z.1)) =
      mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
        (range IB) z.1 0
    rw [map_zero]
  · rfl

omit [FiniteDimensional ℝ E] [ENat.LEInfty (minSmoothness ℝ 3)]
    [FiniteDimensional ℝ EB] in
private lemma lieBracket_product_separated
    (A : EB → EB) (L R : E → E) (a : EB) (y : E)
    (hA : DifferentiableAt ℝ A a) (hL : DifferentiableAt ℝ L y)
    (hR : DifferentiableAt ℝ R y) :
    VectorField.lieBracket ℝ (fun z : EB × E => (0, L z.2))
        (fun z : EB × E => (A z.1, R z.2)) (a, y) =
      (0, VectorField.lieBracket ℝ L R y) := by
  have hAc : DifferentiableAt ℝ (fun z : EB × E => A z.1) (a, y) :=
    hA.comp (a, y) differentiableAt_fst
  have hLc : DifferentiableAt ℝ (fun z : EB × E => L z.2) (a, y) :=
    hL.comp (a, y) differentiableAt_snd
  have hRc : DifferentiableAt ℝ (fun z : EB × E => R z.2) (a, y) :=
    hR.comp (a, y) differentiableAt_snd
  have hzero : DifferentiableAt ℝ (fun _ : EB × E => (0 : EB)) (a, y) :=
    differentiableAt_const _
  unfold VectorField.lieBracket
  rw [hAc.fderiv_prodMk hRc, hzero.fderiv_prodMk hLc]
  have dA := fderiv_comp (f := (Prod.fst : EB × E → EB)) (g := A)
    (a, y) hA differentiableAt_fst
  have dL := fderiv_comp (f := (Prod.snd : EB × E → E)) (g := L)
    (a, y) hL differentiableAt_snd
  have dR := fderiv_comp (f := (Prod.snd : EB × E → E)) (g := R)
    (a, y) hR differentiableAt_snd
  change fderiv ℝ (fun z : EB × E => A z.1) (a, y) = _ at dA
  change fderiv ℝ (fun z : EB × E => L z.2) (a, y) = _ at dL
  change fderiv ℝ (fun z : EB × E => R z.2) (a, y) = _ at dR
  rw [dA, dL, dR, fderiv_fst, fderiv_snd]
  simp

omit [FiniteDimensional ℝ E] [ENat.LEInfty (minSmoothness ℝ 3)]
    [FiniteDimensional ℝ EB] in
private lemma lieBracketWithin_product_separated
    (A : EB → EB) (L R : E → E) (s : Set EB) (t : Set E) (a : EB) (y : E)
    (hA : DifferentiableWithinAt ℝ A s a)
    (hL : DifferentiableWithinAt ℝ L t y)
    (hR : DifferentiableWithinAt ℝ R t y)
    (hs : UniqueDiffWithinAt ℝ s a) (ht : UniqueDiffWithinAt ℝ t y) :
    VectorField.lieBracketWithin ℝ (fun z : EB × E => (0, L z.2))
        (fun z : EB × E => (A z.1, R z.2)) (s ×ˢ t) (a, y) =
      (0, VectorField.lieBracketWithin ℝ L R t y) := by
  have hzero : DifferentiableWithinAt ℝ (fun _ : EB => (0 : EB)) s a :=
    differentiableWithinAt_const 0
  have dW : fderivWithin ℝ (fun z : EB × E => (A z.1, R z.2))
      (s ×ˢ t) (a, y) =
      (fderivWithin ℝ A s a).prodMap (fderivWithin ℝ R t y) := by
    rw [← mfderivWithin_eq_fderivWithin]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    change mfderivWithin ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
      ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
      (Prod.map A R) (s ×ˢ t) (a, y) = _
    rw [mfderivWithin_prodMap hA.mdifferentiableWithinAt hR.mdifferentiableWithinAt
      hs.uniqueMDiffWithinAt ht.uniqueMDiffWithinAt]
    simp only [mfderivWithin_eq_fderivWithin]
    rfl
  have dV : fderivWithin ℝ (fun z : EB × E => (0, L z.2))
      (s ×ˢ t) (a, y) =
      (fderivWithin ℝ (fun _ : EB => (0 : EB)) s a).prodMap
        (fderivWithin ℝ L t y) := by
    rw [← mfderivWithin_eq_fderivWithin]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    change mfderivWithin ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
      ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
      (Prod.map (fun _ : EB => (0 : EB)) L) (s ×ˢ t) (a, y) = _
    rw [mfderivWithin_prodMap hzero.mdifferentiableWithinAt hL.mdifferentiableWithinAt
      hs.uniqueMDiffWithinAt ht.uniqueMDiffWithinAt]
    simp only [mfderivWithin_eq_fderivWithin]
    rfl
  unfold VectorField.lieBracketWithin
  rw [dW, dV]
  simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ EB] in
private lemma product_mpullback_adapted_apply
    (b : B) (u : TangentSpace IB b) (Y : GroupLieAlgebra I G) (z : EB × E)
    (hz : z ∈ (extChartAt (IB.prod I) (b, (1 : G))).target) :
    VectorField.mpullbackWithin (modelWithCornersSelf ℝ (EB × E)) (IB.prod I)
      (extChartAt (IB.prod I) (b, (1 : G))).symm
      (adaptedProductField I IB b u 1 Y) (range (IB.prod I)) z =
    (VectorField.mpullbackWithin (modelWithCornersSelf ℝ EB) IB
        (extChartAt IB b).symm (localTangentFieldAt IB b u) (range IB) z.1,
      VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
        (extChartAt I (1 : G)).symm
        (mulRightInvariantVectorField I (rightInvariantGeneratorAt I 1 Y))
        (range I) z.2) := by
  have hzfull := hz
  simp only [VectorField.mpullbackWithin_apply]
  rw [(isInvertible_mfderivWithin_extChartAt_symm hzfull).inverse_apply_eq]
  rw [extChartAt_prod] at hz
  simp only [PartialEquiv.prod_target] at hz
  rw [extChartAt_prod]
  simp only [PartialEquiv.prod_coe_symm, ModelWithCorners.range_prod,
    adaptedProductField]
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  change (_ = mfderivWithin ((modelWithCornersSelf ℝ EB).prod (modelWithCornersSelf ℝ E))
    (IB.prod I) (Prod.map (extChartAt IB b).symm (extChartAt I (1 : G)).symm)
    (range IB ×ˢ range I) z _)
  rw [mfderivWithin_prodMap
    (mdifferentiableWithinAt_extChartAt_symm hz.1)
    (mdifferentiableWithinAt_extChartAt_symm hz.2)
    (IB.uniqueMDiffOn z.1 (extChartAt_target_subset_range b hz.1))
    (I.uniqueMDiffOn z.2 (extChartAt_target_subset_range 1 hz.2))]
  change (_, _) =
    (mfderivWithin (modelWithCornersSelf ℝ EB) IB (extChartAt IB b).symm
        (range IB) z.1 ((mfderivWithin (modelWithCornersSelf ℝ EB) IB
          (extChartAt IB b).symm (range IB) z.1).inverse _),
      mfderivWithin (modelWithCornersSelf ℝ E) I (extChartAt I (1 : G)).symm
        (range I) z.2 ((mfderivWithin (modelWithCornersSelf ℝ E) I
          (extChartAt I (1 : G)).symm (range I) z.2).inverse _))
  rw [ContinuousLinearMap.IsInvertible.self_apply_inverse
      (isInvertible_mfderivWithin_extChartAt_symm hz.1),
    ContinuousLinearMap.IsInvertible.self_apply_inverse
      (isInvertible_mfderivWithin_extChartAt_symm hz.2)]

/-- On the natural open product domain, the vertical fundamental product field commutes at the
normalized center with the prescribed-value orbit-adapted product field. -/
theorem mlieBracketWithin_verticalFundamental_adaptedProductField_center
    (b : B) (u : TangentSpace IB b) (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracketWithin (IB.prod I)
        (fun z : B × G => (0, mulInvariantVectorField X z.2))
        (adaptedProductField I IB b u 1 Y)
        ((extChartAt IB b).source ×ˢ (Set.univ : Set G)) (b, 1) = 0 := by
  change VectorField.mlieBracketWithin (IB.prod I)
    (verticalFundamentalProductField I IB X) (adaptedProductField I IB b u 1 Y)
    ((extChartAt IB b).source ×ˢ (Set.univ : Set G)) (b, 1) = 0
  let cB := extChartAt IB b
  let cG := extChartAt I (1 : G)
  let aB := cB b
  let aG := cG (1 : G)
  let tB := cB.target
  let tG := cG.target
  let A : EB → EB := VectorField.mpullbackWithin (modelWithCornersSelf ℝ EB) IB
    cB.symm (localTangentFieldAt IB b u) (range IB)
  let L : E → E := VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
    cG.symm (mulInvariantVectorField X) (range I)
  let R : E → E := VectorField.mpullbackWithin (modelWithCornersSelf ℝ E) I
    cG.symm (mulRightInvariantVectorField I (rightInvariantGeneratorAt I 1 Y)) (range I)
  let VP : EB × E → EB × E :=
    VectorField.mpullbackWithin (modelWithCornersSelf ℝ (EB × E)) (IB.prod I)
      (extChartAt (IB.prod I) (b, (1 : G))).symm
      (verticalFundamentalProductField I IB X) (range (IB.prod I))
  let WP : EB × E → EB × E :=
    VectorField.mpullbackWithin (modelWithCornersSelf ℝ (EB × E)) (IB.prod I)
      (extChartAt (IB.prod I) (b, (1 : G))).symm
      (adaptedProductField I IB b u 1 Y) (range (IB.prod I))
  have hAcont : ContDiffWithinAt ℝ 1 A tB aB := by
    apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    convert VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      (((localTangentFieldAt_isSmoothOn IB b u) b (mem_extChartAt_source b)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
      (isOpen_extChartAt_source (I := IB) b).uniqueMDiffOn
      (mem_extChartAt_source b) (m := 1) (n := 2) (by norm_num) using 1
    · simp [tB, cB]
      intro z hz
      exact (chartAt HB b).map_target hz.2
  have hLcont : ContDiffWithinAt ℝ 1 L tG aG := by
    apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    convert VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      ((((contMDiff_mulInvariantVectorField_top I X) (1 : G)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contMDiffWithinAt)
      uniqueMDiffOn_univ (mem_univ (1 : G)) (m := 1) (n := 2) (by norm_num) using 1
    all_goals simp [tG, cG]
  have hRcont : ContDiffWithinAt ℝ 1 R tG aG := by
    apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    convert VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      ((((contMDiff_mulRightInvariantVectorField I
        (rightInvariantGeneratorAt I 1 Y)) (1 : G)).of_le
          (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contMDiffWithinAt)
      uniqueMDiffOn_univ (mem_univ (1 : G)) (m := 1) (n := 2) (by norm_num) using 1
    all_goals simp [tG, cG]
  have hA : DifferentiableWithinAt ℝ A tB aB :=
    hAcont.differentiableWithinAt one_ne_zero
  have hL : DifferentiableWithinAt ℝ L tG aG :=
    hLcont.differentiableWithinAt one_ne_zero
  have hR : DifferentiableWithinAt ℝ R tG aG :=
    hRcont.differentiableWithinAt one_ne_zero
  have hVsep : DifferentiableWithinAt ℝ (fun z : EB × E => ((0 : EB), L z.2))
      (tB ×ˢ tG) (aB, aG) := by
    exact (differentiableWithinAt_const (x := (aB, aG)) (c := (0 : EB))).prodMk
      (hL.comp (f := (Prod.snd : EB × E → E)) (s := tB ×ˢ tG) (t := tG)
        (aB, aG) differentiableWithinAt_snd mapsTo_snd_prod)
  have hWsep : DifferentiableWithinAt ℝ (fun z : EB × E => (A z.1, R z.2))
      (tB ×ˢ tG) (aB, aG) := by
    exact (hA.comp (f := (Prod.fst : EB × E → EB)) (s := tB ×ˢ tG) (t := tB)
      (aB, aG) differentiableWithinAt_fst mapsTo_fst_prod).prodMk
      (hR.comp (f := (Prod.snd : EB × E → E)) (s := tB ×ˢ tG) (t := tG)
        (aB, aG) differentiableWithinAt_snd mapsTo_snd_prod)
  have hcoord : VectorField.lieBracketWithin ℝ VP WP
      (range (IB.prod I)) (extChartAt (IB.prod I) (b, (1 : G)) (b, 1)) = 0 := by
    have hcenter : extChartAt (IB.prod I) (b, (1 : G)) (b, 1) = (aB, aG) := by
      rw [extChartAt_prod]
      rfl
    rw [hcenter]
    have htarget : (extChartAt (IB.prod I) (b, (1 : G))).target = tB ×ˢ tG := by
      rw [extChartAt_prod]
      rfl
    have hVeq (z : EB × E) (hz : z ∈ tB ×ˢ tG) :
        VP z = ((0 : EB), L z.2) := by
      let _I1 : NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ (EB × E)) z) :=
        inferInstanceAs (NormedAddCommGroup (EB × E))
      let _I2 : NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ (EB × E)) z) :=
        inferInstanceAs (NormedSpace ℝ (EB × E))
      have h := product_mpullback_vertical_apply I IB X b z (by
        rw [htarget]
        exact hz)
      change VP z = ((0 : EB), L z.2) at h
      exact h
    have hWeq (z : EB × E) (hz : z ∈ tB ×ˢ tG) :
        WP z = (A z.1, R z.2) := by
      let _I1 : NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ (EB × E)) z) :=
        inferInstanceAs (NormedAddCommGroup (EB × E))
      let _I2 : NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ (EB × E)) z) :=
        inferInstanceAs (NormedSpace ℝ (EB × E))
      have h := product_mpullback_adapted_apply I IB b u Y z (by
        rw [htarget]
        exact hz)
      change WP z = (A z.1, R z.2) at h
      exact h
    have hVactual : DifferentiableWithinAt ℝ VP
        (tB ×ˢ tG) (aB, aG) := by
      apply hVsep.congr
      · intro z hz
        exact hVeq z hz
      · exact hVeq (aB, aG)
          ⟨mem_extChartAt_target (I := IB) b, mem_extChartAt_target (I := I) (1 : G)⟩
    have hWactual : DifferentiableWithinAt ℝ WP
        (tB ×ˢ tG) (aB, aG) := by
      apply hWsep.congr
      · intro z hz
        exact hWeq z hz
      · exact hWeq (aB, aG)
          ⟨mem_extChartAt_target (I := IB) b, mem_extChartAt_target (I := I) (1 : G)⟩
    have hrange : (aB, aG) ∈ range (IB.prod I) := by
      apply extChartAt_target_subset_range (I := IB.prod I) (b, (1 : G))
      rw [htarget]
      change aB ∈ tB ∧ aG ∈ tG
      exact ⟨mem_extChartAt_target (I := IB) b, mem_extChartAt_target (I := I) (1 : G)⟩
    rw [VectorField.lieBracketWithin_of_mem_nhdsWithin
      (by rw [← htarget]; exact
        (extChartAt_target_mem_nhdsWithin (I := IB.prod I) (b, (1 : G))))
      ((IB.prod I).uniqueDiffOn _ hrange) hVactual hWactual]
    rw [VectorField.lieBracketWithin_congr'
      (by intro z hz; exact hVeq z hz)
      (by intro z hz; exact hWeq z hz)
      (by
        change aB ∈ tB ∧ aG ∈ tG
        exact ⟨mem_extChartAt_target (I := IB) b,
          mem_extChartAt_target (I := I) (1 : G)⟩)]
    simp only [aB, aG, cB, cG, tB, tG, A, L, R]
    have hUB : UniqueDiffWithinAt ℝ tB aB := by
      exact uniqueDiffWithinAt_extChartAt_target (I := IB) b
    have hUG : UniqueDiffWithinAt ℝ tG aG := by
      exact uniqueDiffWithinAt_extChartAt_target (I := I) (1 : G)
    rw [lieBracketWithin_product_separated A L R tB tG aB aG hA hL hR hUB hUG]
    have hg := normalizedFundamental_adapted_bracket_zero I X Y
    rw [show VectorField.mlieBracket I (mulInvariantVectorField X)
        (mulRightInvariantVectorField I (rightInvariantGeneratorAt I 1 Y)) 1 =
      VectorField.mlieBracketWithin I (mulInvariantVectorField X)
        (mulRightInvariantVectorField I (rightInvariantGeneratorAt I 1 Y)) univ 1 by rfl,
      VectorField.mlieBracketWithin_apply] at hg
    simp only [preimage_univ, univ_inter] at hg
    let _J1 : NormedAddCommGroup (TangentSpace (modelWithCornersSelf ℝ E) aG) :=
      inferInstanceAs (NormedAddCommGroup E)
    let _J2 : NormedSpace ℝ (TangentSpace (modelWithCornersSelf ℝ E) aG) :=
      inferInstanceAs (NormedSpace ℝ E)
    change (mfderiv I (modelWithCornersSelf ℝ E) cG (1 : G)).inverse
      (VectorField.lieBracketWithin ℝ L R (range I) aG) = 0 at hg
    have hg' := congrArg
      (fun v => mfderiv I (modelWithCornersSelf ℝ E) cG (1 : G) v) hg
    rw [ContinuousLinearMap.IsInvertible.self_apply_inverse
      (isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source (1 : G))),
      map_zero] at hg'
    have hrestrict := VectorField.lieBracketWithin_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin (I := I) (1 : G))
      (I.uniqueDiffOn _ (extChartAt_target_subset_range (1 : G)
        (mem_extChartAt_target (1 : G)))) hL hR
    change VectorField.lieBracketWithin ℝ L R (range I) aG =
      VectorField.lieBracketWithin ℝ L R tG aG at hrestrict
    change (0, VectorField.lieBracketWithin ℝ L R tG aG) = 0
    rw [← hrestrict]
    apply Prod.ext
    · rfl
    · exact hg'
  rw [VectorField.mlieBracketWithin_of_isOpen
    (isOpen_adaptedProductDomain IB b) (adaptedProductDomain_mem IB b (1 : G))]
  rw [show VectorField.mlieBracket (IB.prod I)
      (verticalFundamentalProductField I IB X) (adaptedProductField I IB b u 1 Y) (b, 1) =
    VectorField.mlieBracketWithin (IB.prod I)
      (verticalFundamentalProductField I IB X) (adaptedProductField I IB b u 1 Y)
      univ (b, 1) by rfl,
    VectorField.mlieBracketWithin_apply]
  simp only [preimage_univ, univ_inter]
  rw [hcoord]
  exact map_zero _

end
end YangMills.Geometry.PrincipalOrbitAdapted

