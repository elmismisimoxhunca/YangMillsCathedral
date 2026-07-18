/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerRegularity

/-!
# Permutation symmetry for scalar Schwinger distributions

Osterwalder–Schrader I, printed p. 88, axiom `(E3)`, requires each Euclidean Green's
distribution to be invariant under every permutation of its point arguments. This module constructs
the argument permutation on the actual `n`-point Euclidean configuration space, pulls Schwartz test
functions back through the resulting continuous linear equivalence, and states invariance for the
same positive-arity distribution family.

This is only `(E3)` infrastructure. It supplies no covariance, reflection positivity, clustering,
linear-growth equivalence bridge, reconstruction, or existence claim.
-/

open scoped SchwartzMap

namespace YangMills

/-- A permutation of `n` point labels as a continuous real-linear equivalence of the exact
Euclidean `n`-point configuration space. -/
noncomputable def euclideanNPointPermutation
    (d : EuclideanDimension) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    EuclideanNPointSpace d n ≃L[ℝ] EuclideanNPointSpace d n :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => d.Spacetime) π

/-- Pullback of a scalar Schwartz test function along a point-label permutation. -/
noncomputable def permuteScalarSchwartzTestFunction
    (d : EuclideanDimension) {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ScalarSchwartzTestFunction d n →L[ℂ] ScalarSchwartzTestFunction d n :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclideanNPointPermutation d π)

/-- The permutation pullback evaluates by precomposition with the exact configuration-space
permutation. -/
@[simp] theorem permuteScalarSchwartzTestFunction_apply
    (d : EuclideanDimension) {n : ℕ} (π : Equiv.Perm (Fin n))
    (f : ScalarSchwartzTestFunction d n) (x : EuclideanNPointSpace d n) :
    permuteScalarSchwartzTestFunction d π f x =
      f (euclideanNPointPermutation d π x) :=
  rfl

/-- Scalar Schwinger permutation symmetry `(E3)` for one exact normalized distribution family. -/
structure ScalarSchwingerPermutationSymmetry
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d) : Prop where
  /-- Every positive-arity distribution is invariant under every permutation of those exact point
  labels. -/
  invariant : ∀ (n : PositiveArity) (π : Equiv.Perm (Fin n.value))
    (f : ScalarSchwartzTestFunction d n.value),
    family.positivePoint n (permuteScalarSchwartzTestFunction d π f) =
      family.positivePoint n f

end YangMills
