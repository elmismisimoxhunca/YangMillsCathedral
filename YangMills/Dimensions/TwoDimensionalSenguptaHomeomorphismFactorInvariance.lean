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
equivalences; face regions and areas commute. Under one shared orientation sign, oriented boundary
words are preserved or reversed/flipped, and the source twist `h` is transported as `h` for positive
orientation and `h⁻¹` for negative orientation, and ordinary/twisted
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
  externalEdgeEquiv : SourceEdge ≃ TargetEdge
  internalEdgeEquiv : SourceInternal ≃ TargetInternal
  faceEquiv : SourceFace ≃ TargetFace
  regionEquiv : SourceRegion ≃ TargetRegion
  faceRegion_coherence : ∀ face,
    target.faceRegion (faceEquiv face) = regionEquiv (source.faceRegion face)
  faceArea_coherence : ∀ face, target.faceArea (faceEquiv face) = source.faceArea face
  boundaryWord_coherence : ∀ face,
    target.boundaryWord (faceEquiv face) =
      senguptaTransportedBoundaryWord orientationSign
        (Sum.map externalEdgeEquiv internalEdgeEquiv) (source.boundaryWord face)
  distinguishedFace_coherence : ∀ region,
    faceEquiv (source.distinguishedFace region) =
      target.distinguishedFace (regionEquiv region)
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
