/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerSymmetry

/-!
# Hostile probes for scalar Schwinger permutation symmetry

The probes expose a genuinely nonidentity two-point permutation and ensure that symmetry is tied to
the same distribution family, arity, permutation, and test function.
-/

namespace YangMills.Euclidean.SchwingerSymmetry.Probes

/-- The transposition of the two point labels. -/
def swapTwo : Equiv.Perm (Fin 2) :=
  Equiv.swap 0 1

/-- The quantified permutation family is not reduced to the identity permutation. -/
theorem swapTwo_ne_identity : swapTwo ≠ Equiv.refl (Fin 2) := by
  intro equality
  have atZero := DFunLike.congr_fun equality (0 : Fin 2)
  simp [swapTwo] at atZero

/-- The induced two-point configuration equivalence sends output coordinate zero to input
coordinate one. Thus the implementation cannot ignore the designated transposition. -/
theorem swapTwo_configuration_zero
    (d : EuclideanDimension) (x : EuclideanNPointSpace d 2) :
    euclideanNPointPermutation d swapTwo x (0 : Fin 2) = x (1 : Fin 2) := by
  change (Equiv.piCongrLeft (fun _ : Fin 2 => d.Spacetime) swapTwo) x 0 = x 1
  have h :=
    Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 => d.Spacetime) swapTwo x (1 : Fin 2)
  simpa [swapTwo] using h

/-- The induced two-point configuration equivalence sends output coordinate one to input
coordinate zero. -/
theorem swapTwo_configuration_one
    (d : EuclideanDimension) (x : EuclideanNPointSpace d 2) :
    euclideanNPointPermutation d swapTwo x (1 : Fin 2) = x (0 : Fin 2) := by
  change (Equiv.piCongrLeft (fun _ : Fin 2 => d.Spacetime) swapTwo) x 1 = x 0
  have h :=
    Equiv.piCongrLeft_apply_apply (fun _ : Fin 2 => d.Spacetime) swapTwo x (0 : Fin 2)
  simpa [swapTwo] using h

/-- Scalar permutation symmetry applies to the genuinely swapped two-point pullback, not only to an
abstract identity permutation. -/
theorem exact_two_point_swap_invariance
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (symmetry : ScalarSchwingerPermutationSymmetry family)
    (f : ScalarSchwartzTestFunction d PositiveArity.two.value) :
    family.positivePoint PositiveArity.two
        (permuteScalarSchwartzTestFunction d swapTwo f) =
      family.positivePoint PositiveArity.two f :=
  symmetry.invariant PositiveArity.two swapTwo f

/-- The symmetry projection retains the exact family, arity, permutation, and test function. -/
theorem exact_permutation_invariance
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (symmetry : ScalarSchwingerPermutationSymmetry family)
    (n : PositiveArity) (π : Equiv.Perm (Fin n.value))
    (f : ScalarSchwartzTestFunction d n.value) :
    family.positivePoint n (permuteScalarSchwartzTestFunction d π f) =
      family.positivePoint n f :=
  symmetry.invariant n π f

/-- A changed value under the exact designated permutation contradicts `(E3)`; an unrelated
symmetric family cannot discharge the requirement. -/
theorem permutation_value_replacement_blocked
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    (symmetry : ScalarSchwingerPermutationSymmetry family)
    (n : PositiveArity) (π : Equiv.Perm (Fin n.value))
    (f : ScalarSchwartzTestFunction d n.value)
    (hmismatch :
      family.positivePoint n (permuteScalarSchwartzTestFunction d π f) ≠
        family.positivePoint n f) : False :=
  hmismatch (symmetry.invariant n π f)

end YangMills.Euclidean.SchwingerSymmetry.Probes
