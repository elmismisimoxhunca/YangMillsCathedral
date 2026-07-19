/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSPositiveHalfLineSchwartzQuotient
import YangMills.Foundation.Dimensions

/-!
# Acceptance data for the OS positive-half-space completed tensor product

OS-I, printed pp. 86–87, defines
`𝒮(ℝ⁴₊) = 𝒮(ℝ₊) ⊗̂ 𝒮(ℝ³)` and then its iterated completed tensor powers. The exact Hausdorff
locally convex half-line quotient is now available, while ordinary spatial tests are Schwartz maps
on the neutral real spatial `ℝ³` selected by four-dimensional spacetime. This module states the
source-facing scalar-valued completion surface on those exact factors. The stronger arbitrary-target
projective universal interface remains separate pending authoritative functional-analysis sourcing.

No completed carrier is constructed. A proposed carrier must separately provide an
additive-compatible complete uniformity, Hausdorff local convexity, jointly continuous
noncollapsing pure tensors, dense pure span, and OS-I's scalar-valued extension data. This acceptance
surface is definitionally separate from the finite-sequence direct-sum topology. Explicit nonzero
half-line and spatial bumps prove that any supplied completion has a nonzero pure tensor.
-/

namespace YangMills

noncomputable section

/-- Spatial coordinate index selected by four-dimensional Euclidean spacetime. -/
abbrev OSFourDimensionalSpatialCoordinateIndex :=
  Fin EuclideanDimension.four.spatialDimension

/-- Neutral real Euclidean spatial space of the four-dimensional problem, definitionally `ℝ³`. -/
abbrev OSFourDimensionalSpatialSpace :=
  EuclideanSpace ℝ OSFourDimensionalSpatialCoordinateIndex

/-- Complex Schwartz space on the exact real Euclidean spatial factor `ℝ³`. -/
abbrev OSThreeDimensionalSpatialSchwartzSpace :=
  SchwartzMap OSFourDimensionalSpatialSpace ℂ

/-- The selected spatial factor has real dimension exactly three. -/
@[simp]
theorem finrank_osFourDimensionalSpatialSpace :
    Module.finrank ℝ OSFourDimensionalSpatialSpace = 3 := by
  change Module.finrank ℝ EuclideanDimension.three.Spacetime = 3
  exact EuclideanDimension.finrank_spacetime EuclideanDimension.three

noncomputable local instance halfLineTopologicalAddGroupForTensor :
    IsTopologicalAddGroup OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzIsTopologicalAddGroup

noncomputable local instance halfLineContinuousSMulForTensor :
    ContinuousSMul ℂ OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzContinuousSMul

noncomputable local instance halfLineLocallyConvexForTensor :
    LocallyConvexSpace ℝ OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzLocallyConvexSpace

noncomputable local instance halfLineT2ForTensor : T2Space OSPositiveHalfLineSchwartzSpace :=
  osPositiveHalfLineSchwartzT2Space

noncomputable local instance spatialT2ForTensor :
    T2Space OSThreeDimensionalSpatialSchwartzSpace :=
  SchwartzMap.t2Space

/-- Source-facing acceptance data for one completed positive-half-space tensor factor. The carrier
`T` remains supplied data and is not connected to finite source sequences. The scalar-valued
extension property follows the consequence printed by OS-I; the stronger arbitrary-target
projective universal property remains in separate reusable infrastructure and is not required here. -/
structure OSPositiveHalfSpaceCompletedTensorData
    (T : Type)
    [UniformSpace T] [AddCommGroup T] [Module ℂ T]
    [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
    [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T] where
  /-- Algebraic bilinear pure-tensor map for `𝒮(ℝ₊) ⊗̂ 𝒮(ℝ³)`. -/
  pure : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
    OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] T
  /-- Pure tensors are genuinely jointly continuous. -/
  pure_joint_continuous : Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
    OSThreeDimensionalSpatialSchwartzSpace => pure p.1 p.2)
  /-- Finite linear combinations of pure tensors are dense in the supplied completion. -/
  dense_pure_span : Dense ((Submodule.span ℂ (Set.range
    (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => pure p.1 p.2)) : Submodule ℂ T) : Set T)
  /-- No two nonzero source factors collapse to zero. -/
  pure_ne_zero : ∀ (f : OSPositiveHalfLineSchwartzSpace)
    (g : OSThreeDimensionalSpatialSchwartzSpace), f ≠ 0 → g ≠ 0 → pure f g ≠ 0
  /-- Every jointly continuous scalar-valued bilinear functional extends continuously linearly. -/
  scalarLift : (b : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
    OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] ℂ) →
    Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => b p.1 p.2) → T →L[ℂ] ℂ
  /-- The scalar extension agrees exactly on pure tensors. -/
  scalarLift_pure : ∀ (b : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
    OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => b p.1 p.2))
    (f : OSPositiveHalfLineSchwartzSpace) (g : OSThreeDimensionalSpatialSchwartzSpace),
      scalarLift b hb (pure f g) = b f g

/-- Smooth compactly supported spatial bump centered at the origin. -/
noncomputable def osThreeDimensionalSpatialBump :
    ContDiffBump (0 : OSFourDimensionalSpatialSpace) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Complex spatial Schwartz test induced by the compact bump. -/
noncomputable def osThreeDimensionalSpatialBumpSchwartz :
    OSThreeDimensionalSpatialSchwartzSpace := by
  let bump := osThreeDimensionalSpatialBump
  let complexBump : OSFourDimensionalSpatialSpace → ℂ := Complex.ofRealCLM ∘ bump
  exact (bump.hasCompactSupport.comp_left rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp bump.contDiff)

/-- The spatial bump takes value one at the origin. -/
theorem osThreeDimensionalSpatialBumpSchwartz_zero :
    osThreeDimensionalSpatialBumpSchwartz 0 = 1 := by
  unfold osThreeDimensionalSpatialBumpSchwartz
  change Complex.ofRealCLM (osThreeDimensionalSpatialBump 0) = 1
  rw [osThreeDimensionalSpatialBump.one_of_mem_closedBall]
  · norm_num
  · exact Metric.mem_closedBall_self (le_of_lt osThreeDimensionalSpatialBump.rIn_pos)

/-- The spatial bump is nonzero. -/
theorem osThreeDimensionalSpatialBumpSchwartz_ne_zero :
    osThreeDimensionalSpatialBumpSchwartz ≠ 0 := by
  intro hzero
  have h := congrArg
    (fun f : OSThreeDimensionalSpatialSchwartzSpace => f 0) hzero
  rw [osThreeDimensionalSpatialBumpSchwartz_zero] at h
  simp at h

namespace OSPositiveHalfSpaceCompletedTensorData

variable {T : Type}
variable [UniformSpace T] [AddCommGroup T] [Module ℂ T]
variable [IsUniformAddGroup T] [IsTopologicalAddGroup T] [ContinuousSMul ℂ T]
variable [LocallyConvexSpace ℝ T] [T2Space T] [CompleteSpace T]

/-- Exact pure tensor of the explicit nonzero positive half-line class and spatial bump. -/
def nonzeroBumpPureTensor (D : OSPositiveHalfSpaceCompletedTensorData T) : T :=
  D.pure
    (osPositiveHalfLineSchwartzQuotientMap osPositiveHalfLineBumpSchwartz)
    osThreeDimensionalSpatialBumpSchwartz

/-- Every supplied completed tensor carrier is nontrivial on the explicit two-factor test. -/
theorem nonzeroBumpPureTensor_ne_zero
    (D : OSPositiveHalfSpaceCompletedTensorData T) :
    D.nonzeroBumpPureTensor ≠ 0 :=
  D.pure_ne_zero _ _ osPositiveHalfLineBumpQuotient_ne_zero
    osThreeDimensionalSpatialBumpSchwartz_ne_zero

/-- Pure tensors are genuinely jointly continuous for the exact half-line/spatial factors. -/
theorem continuous_pure_uncurry (D : OSPositiveHalfSpaceCompletedTensorData T) :
    Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => D.pure p.1 p.2) :=
  D.pure_joint_continuous

/-- Agreement on all pure tensors uniquely determines the scalar-valued extension. This follows
from dense pure span and scalar Hausdorffness. -/
theorem scalarLift_unique
    (D : OSPositiveHalfSpaceCompletedTensorData T)
    (b : OSPositiveHalfLineSchwartzSpace →ₗ[ℂ]
      OSThreeDimensionalSpatialSchwartzSpace →ₗ[ℂ] ℂ)
    (hb : Continuous (fun p : OSPositiveHalfLineSchwartzSpace ×
      OSThreeDimensionalSpatialSchwartzSpace => b p.1 p.2))
    (L : T →L[ℂ] ℂ) (hL : ∀ f g, L (D.pure f g) = b f g) :
    L = D.scalarLift b hb := by
  apply ContinuousLinearMap.ext
  intro x
  have hpure : Set.EqOn L (D.scalarLift b hb)
      (Set.range (fun p : OSPositiveHalfLineSchwartzSpace ×
        OSThreeDimensionalSpatialSchwartzSpace => D.pure p.1 p.2)) := by
    rintro _ ⟨⟨f, g⟩, rfl⟩
    rw [hL f g, D.scalarLift_pure b hb f g]
  have hclosure := ContinuousLinearMap.eqOn_closure_span hpure
  exact hclosure (by
    rw [D.dense_pure_span.closure_eq]
    exact Set.mem_univ x)

end OSPositiveHalfSpaceCompletedTensorData

end

end YangMills
