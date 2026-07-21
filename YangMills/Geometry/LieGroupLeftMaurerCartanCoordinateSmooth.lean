/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalConnectionAffineGaugeTransformation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Smooth local coordinates for left Maurer--Cartan trivialization

The left Maurer--Cartan map at `x` is the derivative at `x` of `y ↦ x⁻¹y`. Mathlib's tangent
coordinate transport compares these varying source and target tangent fibers with the fibers over a
fixed chart center. This module proves that the resulting continuous-linear-map coefficient family
is smooth at every chosen center.

This is the exact local derivative ingredient needed to prove smoothness of the invariant metric's
dependent Hom-bundle section. It does not itself construct that section or a Riemannian metric; the
remaining step must reconcile the two nested Hom-bundle coordinate transports with precomposition
of the invariant pairing.
-/

namespace YangMills.Geometry

open scoped Manifold ContDiff

universe uE uH uG

noncomputable section

variable
    {E : Type uE} {H : Type uH}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H G] [LieGroup I ∞ G]

omit [LieGroup I ∞ G] in
/-- The parameterized derivative used below evaluates to the existing canonical left
Maurer--Cartan application, preventing the coordinate bridge from selecting a second derivative
family. -/
@[simp]
theorem parameterizedLeftTranslationDerivative_apply
    (x : G) (v : TangentSpace I x) :
    mfderiv I I (fun y : G => x⁻¹ * y) x v = leftMaurerCartanApply x v :=
  rfl

/-- The exact left Maurer--Cartan derivative family expressed in the tangent coordinates centered at
`center`. Both the varying source fiber at `x` and the varying target fiber at `x⁻¹x` are transported
to the corresponding fixed fibers over `center` and `center⁻¹center`. -/
noncomputable def leftMaurerCartanInTangentCoordinates (center : G) :
    G → (E →L[ℝ] E) :=
  inTangentCoordinates I I (fun x : G => x)
    (fun x : G => x⁻¹ * x)
    (fun x : G => mfderiv I I (fun y : G => x⁻¹ * y) x) center

/-- The exact tangent-coordinate coefficient family of the left Maurer--Cartan derivative is smooth
at its chosen center. -/
theorem leftMaurerCartanInTangentCoordinates_smoothAt (center : G) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (leftMaurerCartanInTangentCoordinates (I := I) center) center := by
  apply ContMDiffAt.mfderiv (n := ∞) (m := ∞)
      (f := fun x : G => fun y : G => x⁻¹ * y) (g := fun x : G => x)
  · exact (((contMDiff_fst (n := ∞)).inv).mul contMDiff_snd).contMDiffAt
  · exact contMDiffAt_id
  · simp

end

end YangMills.Geometry
