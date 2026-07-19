/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate

/-!
# Hostile probes for iterated OS positive-half-space scalar-functional candidates

These probes lock the zero-based intended-factor convention, the exact one-factor candidate anchor,
joint successor continuity, dense pure generation, scalar-only extension semantics, derived
uniqueness, and noncollapse at every finite positive level. They do not characterize tensor topology.
-/

namespace YangMills

namespace OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate.Probes

noncomputable section

/-- Power index zero means one positive-half-space factor, not the scalar sequence component. -/
theorem zero_index_is_one_factor :
    osPositiveHalfSpaceScalarFunctionalTensorFactorCount 0 = 1 :=
  osPositiveHalfSpaceScalarFunctionalTensorFactorCount_zero

/-- Every successor adds exactly one factor under the fixed left association. -/
theorem successor_adds_one_factor (n : ℕ) :
    osPositiveHalfSpaceScalarFunctionalTensorFactorCount (n + 1) =
      osPositiveHalfSpaceScalarFunctionalTensorFactorCount n + 1 :=
  osPositiveHalfSpaceScalarFunctionalTensorFactorCount_succ n

variable {T : ℕ → Type}
variable [∀ n, UniformSpace (T n)] [∀ n, AddCommGroup (T n)] [∀ n, Module ℂ (T n)]
variable [∀ n, IsUniformAddGroup (T n)] [∀ n, IsTopologicalAddGroup (T n)]
variable [∀ n, ContinuousSMul ℂ (T n)] [∀ n, LocallyConvexSpace ℝ (T n)]
variable [∀ n, T2Space (T n)] [∀ n, CompleteSpace (T n)]

/-- The family is anchored to the exact previously sourced one-factor surface. -/
theorem exact_one_factor_surface
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) :
    D.oneFactor.nonzeroBumpPureTensor = D.iteratedBumpPureTensor 0 := by
  rfl

/-- Successor pure tensors must be jointly, rather than merely separately, continuous. -/
theorem exact_successor_joint_continuity
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) (n : ℕ) :
    Continuous (fun p : T n × T 0 => D.stepPure n p.1 p.2) :=
  D.stepPure_joint_continuous n

/-- An invisible disconnected summand is blocked at every successor by dense pure span. -/
theorem exact_successor_dense_pure_span
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) (n : ℕ) :
    Dense ((Submodule.span ℂ (Set.range
      (fun p : T n × T 0 => D.stepPure n p.1 p.2)) :
        Submodule ℂ (T (n + 1))) : Set (T (n + 1))) :=
  D.stepDensePureSpan n

/-- Scalar extension preserves both exact successor factors. -/
theorem exact_successor_scalar_lift_value
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) (n : ℕ)
    (b : T n →ₗ[ℂ] T 0 →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : T n × T 0 => b p.1 p.2))
    (f : T n) (g : T 0) :
    D.stepScalarLift n b hb (D.stepPure n f g) = b f g :=
  D.stepScalarLift_pure n b hb f g

/-- Scalar successor extension uniqueness is derived from density rather than stored independently. -/
theorem exact_successor_scalar_lift_uniqueness
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) (n : ℕ)
    (b : T n →ₗ[ℂ] T 0 →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : T n × T 0 => b p.1 p.2))
    (L : T (n + 1) →L[ℂ] ℂ)
    (hL : ∀ f g, L (D.stepPure n f g) = b f g) :
    L = D.stepScalarLift n b hb :=
  D.stepScalarLift_unique n b hb L hL

/-- The explicit recursively left-associated bump remains nonzero at every positive factor count. -/
theorem iterated_nonzero_bump_retained
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) (n : ℕ) :
    D.iteratedBumpPureTensor n ≠ 0 :=
  D.iteratedBumpPureTensor_ne_zero n

/-- At two factors, omitting either nonzero one-factor input cannot yield the canonical tensor. -/
theorem exact_two_factor_noncollapse
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) :
    D.stepPure 0 D.oneFactor.nonzeroBumpPureTensor D.oneFactor.nonzeroBumpPureTensor ≠ 0 :=
  D.stepPure_ne_zero 0 _ _ D.oneFactor.nonzeroBumpPureTensor_ne_zero
    D.oneFactor.nonzeroBumpPureTensor_ne_zero

/-- The recursively selected two-factor tensor is exactly the pure tensor of both selected factors. -/
theorem exact_two_factor_recursion
    (D : OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate T) :
    D.iteratedBumpPureTensor 1 =
      D.stepPure 0 D.oneFactor.nonzeroBumpPureTensor D.oneFactor.nonzeroBumpPureTensor := by
  rfl

end

end OSPositiveHalfSpaceIteratedScalarFunctionalTensorCandidate.Probes

end YangMills
