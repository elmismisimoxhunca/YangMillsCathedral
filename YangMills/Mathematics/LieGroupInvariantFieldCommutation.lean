/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieGroupInvariantFieldChartTarget

/-!
# Commutation of left- and right-invariant Lie-group fields

Corner-aware identity-chart calculus identifies the exact pullback fields with opposite partials of
one multiplication map. Schwarz cancellation therefore proves that Mathlib's manifold Lie bracket
of a left-invariant and right-invariant field vanishes at the identity. This is a reusable Lie-group
theorem and does not itself assert a principal-form cancellation formula.
-/

namespace YangMills.Mathematics

open Set Function Bundle ChartedSpace
open scoped Manifold ContDiff

universe uE uH uG

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type uG} [Group G] [TopologicalSpace G]
    [ChartedSpace H G] [LieGroup I ∞ G]
    [ENat.LEInfty (minSmoothness ℝ 3)]

/-- Left- and right-invariant vector fields commute at the identity. -/
theorem mlieBracket_mulInvariant_mulRightInvariant_identity
    (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 = 0 := by
  let c := extChartAt I (1 : G)
  let a : E := c (1 : G)
  let t : Set E := c.target
  let F : E × E → E := fun z => c (c.symm z.1 * c.symm z.2)
  let Xc : E := mfderiv I 𝓘(ℝ, E) c 1 X
  let Yc : E := mfderiv I 𝓘(ℝ, E) c 1 Y
  have ha : a ∈ t := by
    dsimp [a, t, c]
    exact mem_extChartAt_target 1
  have ht : UniqueDiffOn ℝ t := by
    simpa [t, c] using
      (uniqueMDiffOn_univ.uniqueDiffOn_target_inter (I := I) (1 : G))
  have haa : (a, a) ∈ closure (interior (t ×ˢ t)) := by
    rw [interior_prod_eq, closure_prod_eq]
    exact ⟨extChartAt_target_subset_closure_interior ha,
      extChartAt_target_subset_closure_interior ha⟩
  have hF : ContDiffWithinAt ℝ 2 F (t ×ˢ t) (a, a) := by
    exact (contDiffWithinAt_extChartAt_mul_identity I).mono (prod_mono
      (extChartAt_target_subset_range (I := I) (1 : G))
      (extChartAt_target_subset_range (I := I) (1 : G)))
  have hFsecond_eq : Set.EqOn (fun z : E => F (a, z)) id t := by
    intro z hz
    change c (c.symm a * c.symm z) = z
    rw [show c.symm a = (1 : G) by simp [a, c], one_mul]
    exact c.right_inv hz
  have hFfirst_eq : Set.EqOn (fun z : E => F (z, a)) id t := by
    intro z hz
    change c (c.symm z * c.symm a) = z
    rw [show c.symm a = (1 : G) by simp [a, c], mul_one]
    exact c.right_inv hz
  have hsecond : fderivWithin ℝ F (t ×ˢ t) (a, a) (0, Xc) = Xc := by
    have hpair : DifferentiableWithinAt ℝ (fun z : E => (a, z)) t a := by fun_prop
    have hchain := fderivWithin_comp (𝕜 := ℝ) (f := fun z : E => (a, z))
      (g := F) (s := t) (t := t ×ˢ t) a
      (hF.differentiableWithinAt (by norm_num)) hpair
      (fun z hz => ⟨ha, hz⟩) (ht a ha)
    have hcongr := fderivWithin_congr (𝕜 := ℝ) hFsecond_eq (hFsecond_eq ha)
    have happ := congrArg (fun L : E →L[ℝ] E => L Xc) hchain
    change (fderivWithin ℝ (fun z : E => F (a, z)) t a) Xc = _ at happ
    rw [hcongr, fderivWithin_id (ht a ha)] at happ
    have hpair_deriv :
        fderivWithin ℝ (fun z : E => (a, z)) t a =
          (ContinuousLinearMap.inr ℝ E E) := by
      have hp := (differentiableWithinAt_const (c := a) |>.fderivWithin_prodMk
        differentiableWithinAt_id (ht a ha))
      rw [fderivWithin_const_apply a, fderivWithin_id (ht a ha)] at hp
      simpa [id_eq, ContinuousLinearMap.inr] using hp
    rw [hpair_deriv] at happ
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.inr_apply] using happ.symm
  have hfirst : fderivWithin ℝ F (t ×ˢ t) (a, a) (Yc, 0) = Yc := by
    have hpair : DifferentiableWithinAt ℝ (fun z : E => (z, a)) t a := by fun_prop
    have hchain := fderivWithin_comp (𝕜 := ℝ) (f := fun z : E => (z, a))
      (g := F) (s := t) (t := t ×ˢ t) a
      (hF.differentiableWithinAt (by norm_num)) hpair
      (fun z hz => ⟨hz, ha⟩) (ht a ha)
    have hcongr := fderivWithin_congr (𝕜 := ℝ) hFfirst_eq (hFfirst_eq ha)
    have happ := congrArg (fun L : E →L[ℝ] E => L Yc) hchain
    change (fderivWithin ℝ (fun z : E => F (z, a)) t a) Yc = _ at happ
    rw [hcongr, fderivWithin_id (ht a ha)] at happ
    have hpair_deriv :
        fderivWithin ℝ (fun z : E => (z, a)) t a =
          (ContinuousLinearMap.inl ℝ E E) := by
      have hp := (differentiableWithinAt_id.fderivWithin_prodMk
        (differentiableWithinAt_const (c := a)) (ht a ha))
      rw [fderivWithin_id (ht a ha), fderivWithin_const_apply a] at hp
      simpa [id_eq, ContinuousLinearMap.inl] using hp
    rw [hpair_deriv] at happ
    simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.inl_apply] using happ.symm
  have hmixed := lieBracketWithin_mixed_partial_eq_zero F t a Xc Yc
    ht ha haa hF hsecond hfirst
  let L : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm
    (mulInvariantVectorField X) (range I)
  let R : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I c.symm
    (mulRightInvariantVectorField I Y) (range I)
  let P : E → E := fun z => fderivWithin ℝ F (t ×ˢ t) (z, a) (0, Xc)
  let Q : E → E := fun z => fderivWithin ℝ F (t ×ˢ t) (a, z) (Yc, 0)
  have hLcont : ContDiffWithinAt ℝ 1 L t a := by
    apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    convert VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      ((((contMDiff_mulInvariantVectorField_top I X) (1 : G)).of_le (by norm_num)).contMDiffWithinAt)
      uniqueMDiffOn_univ (mem_univ (1 : G)) (m := 1) (n := 2) (by norm_num) using 1
    all_goals simp [t, c]
  have hLdiff : DifferentiableWithinAt ℝ L t a :=
    hLcont.differentiableWithinAt one_ne_zero
  have hRcont : ContDiffWithinAt ℝ 1 R t a := by
    apply contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp
    convert VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
      ((((contMDiff_mulRightInvariantVectorField I Y) (1 : G)).of_le (by norm_num)).contMDiffWithinAt)
      uniqueMDiffOn_univ (mem_univ (1 : G)) (m := 1) (n := 2) (by norm_num) using 1
    all_goals simp [t, c]
  have hRdiff : DifferentiableWithinAt ℝ R t a :=
    hRcont.differentiableWithinAt one_ne_zero
  have hleft_chart : Set.EqOn L P t := by
    intro z hz
    change extChartCoordinateField I (1 : G) (mulInvariantVectorField X) z = _
    simpa only [c, a, t, F, Xc, Function.comp_apply] using
      extChartCoordinateField_mulInvariantVectorField_eq_secondPartial_target I X z hz
  have hright_chart : Set.EqOn R Q t := by
    simpa only [c, a, t, F, Yc, R, Q] using
      mpullbackWithin_mulRightInvariantVectorField_eq_firstPartial_on_target I Y
  have hcoord : VectorField.lieBracketWithin ℝ L R (range I) a = 0 := by
    rw [VectorField.lieBracketWithin_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin (I := I) (1 : G))
      (I.uniqueDiffOn a ((extChartAt_target_subset_range (I := I) (1 : G)) ha)) hLdiff hRdiff]
    rw [VectorField.lieBracketWithin_congr' hleft_chart hright_chart ha]
    exact hmixed
  let _I1 : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) a) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _I2 : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) a) := ‹NormedSpace ℝ E›
  rw [show VectorField.mlieBracket I (mulInvariantVectorField X)
      (mulRightInvariantVectorField I Y) 1 =
      VectorField.mlieBracketWithin I (mulInvariantVectorField X)
        (mulRightInvariantVectorField I Y) univ 1 by rfl,
    VectorField.mlieBracketWithin_apply]
  simp only [preimage_univ, univ_inter]
  change (mfderiv I 𝓘(ℝ, E) c 1).inverse
    (VectorField.lieBracketWithin ℝ L R (range I) a) = 0
  rw [hcoord]
  exact map_zero _

end

end YangMills.Mathematics
