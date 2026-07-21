/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.PartialDiffeomorphLieBracket

namespace YangMills.Mathematics.PartialDiffeomorphLieBracket.Probes

open Set
open scoped Manifold ContDiff

universe uE uE' uH uH' uM uM'

noncomputable section

variable {E : Type uE} {E' : Type uE'} {H : Type uH} {H' : Type uH'}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {M : Type uM} {M' : Type uM'} [TopologicalSpace M] [TopologicalSpace M']
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    [ChartedSpace H M] [ChartedSpace H' M']
    [IsManifold I ∞ M] [IsManifold I' ∞ M']

/-- A target zero bracket pulls back to the canonical restricted source. -/
theorem exact_target_open_zero_transport
    (e : OpenPartialHomeomorph M M') {t : Set M'}
    (ht : IsOpen t) (htTarget : t ⊆ e.target)
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
      (e.source ∩ e ⁻¹' t) x = 0 :=
  OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_targetOpen
    e ht htTarget he heInv hxSource hxt hV hW hzero

/-- A nonzero pulled bracket contradicts exact partial-diffeomorphism naturality. -/
theorem nonzero_target_open_pullback_blocked
    (e : OpenPartialHomeomorph M M') {t : Set M'}
    (ht : IsOpen t) (htTarget : t ⊆ e.target)
    (he : ContMDiffOn I I' ∞ e e.source)
    (heInv : ContMDiffOn I' I ∞ e.symm e.target)
    {V W : (y : M') → TangentSpace I' y} {x : M}
    (hxSource : x ∈ e.source) (hxt : e x ∈ t)
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, V y⟩ : TangentBundle I' M')) t (e x))
    (hW : MDifferentiableWithinAt I' I'.tangent
      (fun y => (⟨y, W y⟩ : TangentBundle I' M')) t (e x))
    (hzero : VectorField.mlieBracketWithin I' V W t (e x) = 0)
    (nonzero : VectorField.mlieBracketWithin I
      (VectorField.mpullbackWithin I I' e V (e.source ∩ e ⁻¹' t))
      (VectorField.mpullbackWithin I I' e W (e.source ∩ e ⁻¹' t))
      (e.source ∩ e ⁻¹' t) x ≠ 0) : False :=
  nonzero (OpenPartialHomeomorph.mlieBracketWithin_mpullbackWithin_eq_zero_targetOpen
    e ht htTarget he heInv hxSource hxt hV hW hzero)

end

end YangMills.Mathematics.PartialDiffeomorphLieBracket.Probes
