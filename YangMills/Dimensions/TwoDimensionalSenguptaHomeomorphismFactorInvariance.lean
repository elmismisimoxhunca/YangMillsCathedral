/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors

/-!
# One-pair Sengupta homeomorphism factor invariance

This file isolates a finite-face candidate comparison toward Sengupta Definition 7.6, Fact 3. Source
and target presentations are related by explicit external/internal edge, face, and region
equivalences; face regions and oriented words commute, while only mapped region-total areas are fixed
as required by the source. Fact 1 permits simplex-area redistribution and Fact 0 removes the twist
face choice. Each face records whether its independently chosen simplex orientation is reversed, while the global
source sign transports the twist `h` as `h` for positive orientation and `h⁻¹` for negative
orientation. Keeping these separate is essential for nonorientable surfaces, and ordinary/twisted
fixed-boundary factors are required to agree after transporting the external field.

This remains an uninhabited combinatorial comparison. It does not construct an area-preserving
surface homeomorphism, prove reparameterization coherence of actual curves, or quantify over every
source-valid homeomorphism required by the full Fact 3.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

universe uCover uSourceEdge uTargetEdge uSourceInternal uTargetInternal
  uSourceFace uTargetFace uSourceRegion uTargetRegion

/-- Orientation sign in Sengupta Fact 3. -/
inductive SenguptaHomeomorphismOrientationSign
  | positive
  | negative
  deriving DecidableEq

/-- Orientation reversal sends the central bundle class to its inverse. -/
def senguptaTransportedBundleClass {G : Type*} [Group G]
    (sign : SenguptaHomeomorphismOrientationSign) (bundleClass : G) : G :=
  match sign with
  | .positive => bundleClass
  | .negative => bundleClass⁻¹

/-- Map one oriented edge without changing its orientation sign. -/
def senguptaMapOrientedEdge {Edge TargetEdge : Type*}
    (edgeMap : Edge → TargetEdge) : OrientedEdge Edge → OrientedEdge TargetEdge
  | .forward edge => .forward (edgeMap edge)
  | .reverse edge => .reverse (edgeMap edge)

/-- Transport an oriented boundary word. Negative orientation also reverses traversal order and
flips every edge, so its holonomy is inverted. -/
def senguptaTransportedBoundaryWord {Edge TargetEdge : Type*}
    (sign : SenguptaHomeomorphismOrientationSign) (edgeMap : Edge → TargetEdge)
    (word : List (OrientedEdge Edge)) : List (OrientedEdge TargetEdge) :=
  match sign with
  | .positive => word.map (senguptaMapOrientedEdge edgeMap)
  | .negative => reverseFiniteOrientedWord (word.map (senguptaMapOrientedEdge edgeMap))

/-- Transport a boundary word using its independently chosen source/target simplex orientation. -/
def senguptaTransportedBoundaryWordByReversal {Edge TargetEdge : Type*}
    (reverseOrientation : Bool) (edgeMap : Edge → TargetEdge)
    (word : List (OrientedEdge Edge)) : List (OrientedEdge TargetEdge) :=
  if reverseOrientation then
    reverseFiniteOrientedWord (word.map (senguptaMapOrientedEdge edgeMap))
  else word.map (senguptaMapOrientedEdge edgeMap)

/-- Transport an external field through an edge equivalence. -/
def senguptaTransportExternalField
    {SourceEdge : Type uSourceEdge} {TargetEdge : Type uTargetEdge}
    {G : Type*} (edgeEquiv : SourceEdge ≃ TargetEdge)
    (source : SourceEdge → G) : TargetEdge → G :=
  fun edge => source (edgeEquiv.symm edge)

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {SourceEdge : Type uSourceEdge} {TargetEdge : Type uTargetEdge}
    {SourceInternal : Type uSourceInternal} [Fintype SourceInternal]
    {TargetInternal : Type uTargetInternal} [Fintype TargetInternal]
    {SourceFace : Type uSourceFace} [Fintype SourceFace] [DecidableEq SourceFace]
    {TargetFace : Type uTargetFace} [Fintype TargetFace] [DecidableEq TargetFace]
    {SourceRegion : Type uSourceRegion} [DecidableEq SourceRegion]
    {TargetRegion : Type uTargetRegion} [DecidableEq TargetRegion]
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {source : TwoDimensionalSenguptaTriangulatedRegionData
      SourceEdge SourceInternal SourceFace SourceRegion}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {bundleClass : CoverGroup}

/-- Factor-level certificate for one candidate area-preserving homeomorphism comparison. -/
structure TwoDimensionalSenguptaHomeomorphismFactorInvarianceData where
  coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity
  bundleClass_central : ∀ element, bundleClass * element = element * bundleClass
  orientationSign : SenguptaHomeomorphismOrientationSign
  /-- Simplex boundary orientations are independent of the global `h`/`h⁻¹` sign in the
  nonorientable case. -/
  faceOrientationReversed : SourceFace → Bool
  externalEdgeEquiv : SourceEdge ≃ TargetEdge
  internalEdgeEquiv : SourceInternal ≃ TargetInternal
  faceEquiv : SourceFace ≃ TargetFace
  regionEquiv : SourceRegion ≃ TargetRegion
  faceRegion_coherence : ∀ face,
    target.faceRegion (faceEquiv face) = regionEquiv (source.faceRegion face)
  /-- Fact 3 assumes equality only of total area. Fact 1 removes dependence on simplex allocations. -/
  regionArea_coherence : ∀ region,
    target.regionArea (regionEquiv region) = source.regionArea region
  boundaryWord_coherence : ∀ face,
    target.boundaryWord (faceEquiv face) =
      senguptaTransportedBoundaryWordByReversal (faceOrientationReversed face)
        (Sum.map externalEdgeEquiv internalEdgeEquiv) (source.boundaryWord face)
  ordinaryFactor_eq : ∀ region external,
    senguptaTriangulatedRegionFactor source coverDensity region external =
      senguptaTriangulatedRegionFactor target coverDensity (regionEquiv region)
        (senguptaTransportExternalField externalEdgeEquiv external)
  twistedFactor_eq : ∀ region external,
    senguptaTriangulatedTwistedRegionFactor source coverDensity bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor target coverDensity
        (senguptaTransportedBundleClass orientationSign bundleClass) (regionEquiv region)
        (senguptaTransportExternalField externalEdgeEquiv external)

namespace TwoDimensionalSenguptaHomeomorphismFactorInvarianceData

/-- Negative orientation uses exactly the inverse bundle class. -/
@[simp]
theorem transportedBundleClass_negative
    (data : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
      (coverDensity := coverDensity) (source := source) (target := target)
      (bundleClass := bundleClass))
    (negative : data.orientationSign = .negative) :
    senguptaTransportedBundleClass data.orientationSign bundleClass = bundleClass⁻¹ := by
  rw [negative]
  rfl

end TwoDimensionalSenguptaHomeomorphismFactorInvarianceData

end

end YangMills.Dimensions
