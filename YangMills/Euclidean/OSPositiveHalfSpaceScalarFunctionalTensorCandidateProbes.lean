/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSPositiveHalfSpaceScalarFunctionalTensorCandidate

/-!
# Hostile probes for the OS positive-half-space scalar-functional tensor candidate

The probes require both exact factors, joint continuity, dense pure span, scalar extension, and a
nonzero explicit pure tensor. They neither construct nor characterize a completed tensor product.
-/

namespace YangMills.OSPositiveHalfSpaceScalarFunctionalTensorCandidate.Probes

noncomputable section

noncomputable local instance halfLineTopologicalAddGroupForProbes :
    IsTopologicalAddGroup OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzIsTopologicalAddGroup

noncomputable local instance halfLineContinuousSMulForProbes :
    ContinuousSMul ℂ OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzContinuousSMul

noncomputable local instance halfLineLocallyConvexForProbes :
    LocallyConvexSpace ℝ OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzLocallyConvexSpace

noncomputable local instance halfLineT2ForProbes : T2Space OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzT2Space

noncomputable local instance spatialT2ForProbes :
    T2Space OSThreeDimensionalSpatialSchwartzSpace :=
  SchwartzMap.t2Space

/-- The spatial factor is tied to the three spatial coordinates of four-dimensional spacetime. -/
theorem exact_four_dimensional_spatial_dimension :
    Module.finrank ℝ OSFourDimensionalSpatialSpace =
      EuclideanDimension.four.spatialDimension := by
  rw [finrank_osFourDimensionalSpatialSpace]
  rfl

/-- The spatial factor is genuinely nonzero. -/
theorem nonzero_spatial_factor_retained :
    osThreeDimensionalSpatialBumpSchwartz ≠ 0 :=
  osThreeDimensionalSpatialBumpSchwartz_ne_zero

variable {T : Type}
variable [UniformSpace T] [AddCommGroup T] [Module ℂ T]
variable [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
variable [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T]

/-- Any supplied scalar-functional candidate retains both explicit nonzero factors. -/
theorem exact_nonzero_two_factor_tensor
    (D : OSPositiveHalfSpaceScalarFunctionalTensorCandidate T) :
    D.pure
      (osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz)
      osThreeDimensionalSpatialBumpSchwartz ≠ 0 :=
  D.nonzeroBumpPureTensor_ne_zero

/-- The source-facing pure map is genuinely jointly continuous, not only separately continuous. -/
theorem exact_joint_pure_continuity
    (D : OSPositiveHalfSpaceScalarFunctionalTensorCandidate T) :
    Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => D.pure p.1 p.2) :=
  D.continuous_pure_uncurry

/-- A disconnected candidate summand invisible to all pure tensors is blocked by density. -/
theorem exact_dense_pure_span
    (D : OSPositiveHalfSpaceScalarFunctionalTensorCandidate T) :
    Dense ((Submodule.span ℂ (Set.range
      (fun p : OSPositiveHalfLineSchwartzSpace ×
        OSThreeDimensionalSpatialSchwartzSpace =>
          D.pure p.1 p.2)) : Submodule ℂ T) : Set T) :=
  D.dense_pure_span

/-- OS-I's scalar-valued extension data retains the exact two-factor value. -/
theorem exact_scalar_lift_value
    (D : OSPositiveHalfSpaceScalarFunctionalTensorCandidate T)
    (b : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
      OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => b p.1 p.2)) :
    D.scalarLift b hb D.nonzeroBumpPureTensor =
      b (osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz)
        osThreeDimensionalSpatialBumpSchwartz :=
  D.scalarLift_pure b hb _ _

/-- A disconnected scalar extension agreeing on every pure tensor is blocked by density. -/
theorem exact_scalar_lift_uniqueness
    (D : OSPositiveHalfSpaceScalarFunctionalTensorCandidate T)
    (b : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
      OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => b p.1 p.2))
    (L : T →L[ℂ] ℂ) (hL : ∀ f g, L (D.pure f g) = b f g) :
    L = D.scalarLift b hb :=
  D.scalarLift_unique b hb L hL

end

end YangMills.OSPositiveHalfSpaceScalarFunctionalTensorCandidate.Probes
