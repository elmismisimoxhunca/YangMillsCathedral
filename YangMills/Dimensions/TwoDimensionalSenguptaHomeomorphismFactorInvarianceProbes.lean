/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaHomeomorphismFactorInvariance

/-! Hostile probes for one-pair Sengupta homeomorphism factor invariance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaHomeomorphismFactorInvariance.Probes

open YangMills.Mathematics
open scoped ENNReal

noncomputable section

variable
    {CoverGroup : Type*} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {SourceEdge TargetEdge SourceInternal TargetInternal SourceFace TargetFace
      SourceRegion TargetRegion : Type*}
    [Fintype SourceInternal] [Fintype TargetInternal]
    [Fintype SourceFace] [DecidableEq SourceFace]
    [Fintype TargetFace] [DecidableEq TargetFace]
    [DecidableEq SourceRegion] [DecidableEq TargetRegion]
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {source : TwoDimensionalSenguptaTriangulatedRegionData
      SourceEdge SourceInternal SourceFace SourceRegion}
    {target : TwoDimensionalSenguptaTriangulatedRegionData
      TargetEdge TargetInternal TargetFace TargetRegion}
    {bundleClass : CoverGroup}
    (data : TwoDimensionalSenguptaHomeomorphismFactorInvarianceData
      (coverDensity := coverDensity) (source := source) (target := target)
      (bundleClass := bundleClass))

/-- Oriented boundary words commute with the full edge transport and the selected orientation
sign, including reversal in the negative case. -/
theorem exact_boundary_word_transport (face : SourceFace) :
    target.boundaryWord (data.faceEquiv face) =
      senguptaTransportedBoundaryWordByReversal (data.faceOrientationReversed face)
        (Sum.map data.externalEdgeEquiv data.internalEdgeEquiv) (source.boundaryWord face) :=
  data.boundaryWord_coherence face

include data in
/-- The candidate is tied to a normalized nonzero heat-density semigroup. -/
theorem exact_positive_time_density_measure {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t Set.univ = 1 ∧
      normalizedCompactHaarDensitySemigroupMeasure coverDensity t ≠ 0 :=
  ⟨data.coverSemigroup.measure_univ ht, data.coverSemigroup.measure_ne_zero ht⟩

include data in
/-- The transported bundle-class representative is central. -/
theorem exact_central_twist (element : CoverGroup) :
    bundleClass * element = element * bundleClass :=
  data.bundleClass_central element

/-- Face-region transport and source-required mapped region-total area are exact. -/
theorem exact_face_region_and_total_area (face : SourceFace) (region : SourceRegion) :
    target.faceRegion (data.faceEquiv face) = data.regionEquiv (source.faceRegion face) ∧
    target.regionArea (data.regionEquiv region) = source.regionArea region :=
  ⟨data.faceRegion_coherence face, data.regionArea_coherence region⟩

include data in
/-- Hostile total-area probe: simplex allocations and twist faces may vary, but total area may not. -/
theorem changed_mapped_region_total_blocked (region : SourceRegion)
    (changed : target.regionArea (data.regionEquiv region) ≠ source.regionArea region) : False :=
  changed (data.regionArea_coherence region)

/-- Hostile ordinary Fact 3 probe. -/
theorem changed_ordinary_homeomorphism_factor_blocked
    (region : SourceRegion) (external : SourceEdge → CoverGroup)
    (changed : senguptaTriangulatedRegionFactor source coverDensity region external ≠
      senguptaTriangulatedRegionFactor target coverDensity (data.regionEquiv region)
        (senguptaTransportExternalField data.externalEdgeEquiv external)) : False :=
  changed (data.ordinaryFactor_eq region external)

/-- Hostile signed-twist Fact 3 probe. -/
theorem changed_twisted_homeomorphism_factor_blocked
    (region : SourceRegion) (external : SourceEdge → CoverGroup)
    (changed : senguptaTriangulatedTwistedRegionFactor source coverDensity
        bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor target coverDensity
        (senguptaTransportedBundleClass data.orientationSign bundleClass)
        (data.regionEquiv region)
        (senguptaTransportExternalField data.externalEdgeEquiv external)) : False :=
  changed (data.twistedFactor_eq region external)

omit [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup] [CompactSpace CoverGroup]
    [MeasurableSpace CoverGroup] [BorelSpace CoverGroup] in
/-- The two global source signs have exact `h`/`h⁻¹` semantics. The displayed word formulas remain
helper specializations; actual nonorientable face reversal choices are stored independently. -/
theorem exact_orientation_sign_transport (word : List (OrientedEdge SourceEdge))
    (edgeMap : SourceEdge → TargetEdge) :
    senguptaTransportedBundleClass .positive bundleClass = bundleClass ∧
    senguptaTransportedBundleClass .negative bundleClass = bundleClass⁻¹ ∧
    senguptaTransportedBoundaryWord .positive edgeMap word =
      word.map (senguptaMapOrientedEdge edgeMap) ∧
    senguptaTransportedBoundaryWord .negative edgeMap word =
      reverseFiniteOrientedWord (word.map (senguptaMapOrientedEdge edgeMap)) :=
  ⟨rfl, rfl, rfl, rfl⟩

end

end YangMills.Dimensions.TwoDimensionalSenguptaHomeomorphismFactorInvariance.Probes
