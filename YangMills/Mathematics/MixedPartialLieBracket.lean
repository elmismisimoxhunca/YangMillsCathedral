/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Calculus.DifferentialForm.VectorField
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Lie brackets of mixed partial derivative fields

Schwarz symmetry proves that the two vector fields obtained from opposite partial derivatives of one
`C²` map have zero Lie bracket at their common base point when the two selected first partials there
recover their designated directions. The within-set form retains unique
differentiability and closure-of-interior hypotheses and is suitable for corner-model chart ranges.
This is reusable normed-space calculus; it does not assert the remaining chart identification for
left- and right-invariant Lie-group fields.
-/

namespace YangMills.Mathematics

open Set
open scoped ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The two vector-space fields obtained from opposite partial derivatives of one `C²` map
have zero Lie bracket at the common base point when the selected first partials recover `X` and `Y`.
This is the exact Schwarz bridge needed after
putting group multiplication into one centered chart. -/
theorem lieBracket_mixed_partial_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E × E → E) (a X Y : E) (hF : ContDiffAt ℝ 2 F (a, a))
    (hsecond : fderiv ℝ F (a, a) (0, X) = X)
    (hfirst : fderiv ℝ F (a, a) (Y, 0) = Y) :
    VectorField.lieBracket ℝ
      (fun x => fderiv ℝ F (x, a) (0, X))
      (fun x => fderiv ℝ F (a, x) (Y, 0)) a = 0 := by
  have hdF : DifferentiableAt ℝ (fderiv ℝ F) (a, a) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm := hF.isSymmSndFDerivAt (by norm_num)
  have hrightPair : HasFDerivAt (fun x : E => (a, x))
      (ContinuousLinearMap.inr ℝ E E) a := by
    fun_prop
  have hleftPair : HasFDerivAt (fun x : E => (x, a))
      (ContinuousLinearMap.inl ℝ E E) a := by
    fun_prop
  have hright :
      fderiv ℝ (fun x : E => fderiv ℝ F (a, x) (Y, 0)) a X =
        fderiv ℝ (fderiv ℝ F) (a, a) (0, X) (Y, 0) := by
    have hdF_right : HasFDerivAt (fun x : E => fderiv ℝ F (a, x))
        ((fderiv ℝ (fderiv ℝ F) (a, a)).comp (ContinuousLinearMap.inr ℝ E E)) a := by
      exact hdF.hasFDerivAt.comp (f := fun x : E => (a, x)) a hrightPair
    have hcomp := (ContinuousLinearMap.apply ℝ E (Y, 0)).hasFDerivAt.comp a hdF_right
    have heq := congrArg (fun L : E →L[ℝ] E => L X) hcomp.fderiv
    change fderiv ℝ (fun x : E => fderiv ℝ F (a, x) (Y, 0)) a X = _
    exact heq
  have hleft :
      fderiv ℝ (fun x : E => fderiv ℝ F (x, a) (0, X)) a Y =
        fderiv ℝ (fderiv ℝ F) (a, a) (Y, 0) (0, X) := by
    have hdF_left : HasFDerivAt (fun x : E => fderiv ℝ F (x, a))
        ((fderiv ℝ (fderiv ℝ F) (a, a)).comp (ContinuousLinearMap.inl ℝ E E)) a := by
      exact hdF.hasFDerivAt.comp (f := fun x : E => (x, a)) a hleftPair
    have hcomp := (ContinuousLinearMap.apply ℝ E (0, X)).hasFDerivAt.comp a hdF_left
    have heq := congrArg (fun L : E →L[ℝ] E => L Y) hcomp.fderiv
    change fderiv ℝ (fun x : E => fderiv ℝ F (x, a) (0, X)) a Y = _
    exact heq
  rw [VectorField.lieBracket_eq]
  change fderiv ℝ (fun x : E => fderiv ℝ F (a, x) (Y, 0)) a
      (fderiv ℝ F (a, a) (0, X)) -
    fderiv ℝ (fun x : E => fderiv ℝ F (x, a) (0, X)) a
      (fderiv ℝ F (a, a) (Y, 0)) = 0
  rw [hsecond, hfirst, hright, hleft]
  rw [hsymm (0, X) (Y, 0)]
  exact sub_self _

/-- Corner-safe mixed-partial commutation: opposite partial derivative fields of one `C²`
map have zero within-set Lie bracket at their common base point, provided the selected first
partials recover the designated directions there. -/
theorem lieBracketWithin_mixed_partial_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E × E → E) (t : Set E) (a X Y : E)
    (ht : UniqueDiffOn ℝ t) (ha : a ∈ t)
    (haa : (a, a) ∈ closure (interior (t ×ˢ t)))
    (hF : ContDiffWithinAt ℝ 2 F (t ×ˢ t) (a, a))
    (hsecond : fderivWithin ℝ F (t ×ˢ t) (a, a) (0, X) = X)
    (hfirst : fderivWithin ℝ F (t ×ˢ t) (a, a) (Y, 0) = Y) :
    VectorField.lieBracketWithin ℝ
      (fun x => fderivWithin ℝ F (t ×ˢ t) (x, a) (0, X))
      (fun x => fderivWithin ℝ F (t ×ˢ t) (a, x) (Y, 0)) t a = 0 := by
  let S : Set (E × E) := t ×ˢ t
  have hS : UniqueDiffOn ℝ S := ht.prod ht
  have haa_mem : (a, a) ∈ S := ⟨ha, ha⟩
  have hdF : DifferentiableWithinAt ℝ (fderivWithin ℝ F S) S (a, a) :=
    (hF.fderivWithin_right hS (m := 1) (by norm_num) haa_mem).differentiableWithinAt one_ne_zero
  have hsymm := hF.isSymmSndFDerivWithinAt (by norm_num) hS haa haa_mem
  have hrightPair : HasFDerivWithinAt (fun x : E => (a, x))
      (ContinuousLinearMap.inr ℝ E E) t a := by
    exact (by fun_prop : HasFDerivAt (fun x : E => (a, x))
      (ContinuousLinearMap.inr ℝ E E) a).hasFDerivWithinAt
  have hleftPair : HasFDerivWithinAt (fun x : E => (x, a))
      (ContinuousLinearMap.inl ℝ E E) t a := by
    exact (by fun_prop : HasFDerivAt (fun x : E => (x, a))
      (ContinuousLinearMap.inl ℝ E E) a).hasFDerivWithinAt
  have hrightMap : MapsTo (fun x : E => (a, x)) t S := fun x hx => ⟨ha, hx⟩
  have hleftMap : MapsTo (fun x : E => (x, a)) t S := fun x hx => ⟨hx, ha⟩
  have hright :
      fderivWithin ℝ
          (fun x : E => fderivWithin ℝ F S (a, x) (Y, 0)) t a X =
        fderivWithin ℝ (fderivWithin ℝ F S) S (a, a) (0, X) (Y, 0) := by
    have hdF_right : HasFDerivWithinAt
        (fun x : E => fderivWithin ℝ F S (a, x))
        ((fderivWithin ℝ (fderivWithin ℝ F S) S (a, a)).comp
          (ContinuousLinearMap.inr ℝ E E)) t a := by
      exact hdF.hasFDerivWithinAt.comp (f := fun x : E => (a, x))
        (s := t) (t := S) a hrightPair hrightMap
    have hcomp := (ContinuousLinearMap.apply ℝ E (Y, 0)).hasFDerivAt.comp_hasFDerivWithinAt
      a hdF_right
    have heq := congrArg (fun L : E →L[ℝ] E => L X) (hcomp.fderivWithin (ht a ha))
    exact heq
  have hleft :
      fderivWithin ℝ
          (fun x : E => fderivWithin ℝ F S (x, a) (0, X)) t a Y =
        fderivWithin ℝ (fderivWithin ℝ F S) S (a, a) (Y, 0) (0, X) := by
    have hdF_left : HasFDerivWithinAt
        (fun x : E => fderivWithin ℝ F S (x, a))
        ((fderivWithin ℝ (fderivWithin ℝ F S) S (a, a)).comp
          (ContinuousLinearMap.inl ℝ E E)) t a := by
      exact hdF.hasFDerivWithinAt.comp (f := fun x : E => (x, a))
        (s := t) (t := S) a hleftPair hleftMap
    have hcomp := (ContinuousLinearMap.apply ℝ E (0, X)).hasFDerivAt.comp_hasFDerivWithinAt
      a hdF_left
    have heq := congrArg (fun L : E →L[ℝ] E => L Y) (hcomp.fderivWithin (ht a ha))
    exact heq
  rw [VectorField.lieBracketWithin_eq]
  change fderivWithin ℝ
      (fun x : E => fderivWithin ℝ F S (a, x) (Y, 0)) t a
        (fderivWithin ℝ F S (a, a) (0, X)) -
    fderivWithin ℝ
      (fun x : E => fderivWithin ℝ F S (x, a) (0, X)) t a
        (fderivWithin ℝ F S (a, a) (Y, 0)) = 0
  rw [hsecond, hfirst, hright, hleft]
  rw [hsymm (0, X) (Y, 0)]
  exact sub_self _

end

end YangMills.Mathematics
