/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaSubdivisionFactorInvariance

/-! Hostile probes for one-step Sengupta subdivision factor invariance. -/

namespace YangMills.Dimensions.TwoDimensionalSenguptaSubdivisionFactorInvariance.Probes

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal BigOperators

noncomputable section

variable
    {CoverGroup : Type*} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Edge CoarseInternal CoarseFace FineInternal FineFace Region : Type*}
    [Fintype CoarseInternal] [Fintype CoarseFace] [DecidableEq CoarseFace]
    [Fintype FineInternal] [Fintype FineFace] [DecidableEq FineFace]
    [DecidableEq Region]
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {coarse : TwoDimensionalSenguptaTriangulatedRegionData
      Edge CoarseInternal CoarseFace Region}
    {fine : TwoDimensionalSenguptaTriangulatedRegionData
      Edge FineInternal FineFace Region}
    {bundleClass : CoverGroup}
    (data : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := coarse) (fine := fine)
      (bundleClass := bundleClass))

/-- Exact face-region and source-required total-region-area semantics. -/
theorem exact_face_region_and_total_area (fineFace : FineFace) (region : Region) :
    coarse.faceRegion (data.fineFaceToCoarse fineFace) = fine.faceRegion fineFace ∧
      coarse.regionArea region = fine.regionArea region :=
  ⟨data.faceRegion_coherence fineFace, data.regionArea_coherence region⟩

include data in
/-- The candidate is tied to a normalized nonzero density semigroup, blocking the zero-density
surrogate. -/
theorem exact_positive_time_density_measure {t : ℝ} (ht : 0 < t) :
    normalizedCompactHaarDensitySemigroupMeasure coverDensity t Set.univ = 1 ∧
      normalizedCompactHaarDensitySemigroupMeasure coverDensity t ≠ 0 :=
  ⟨data.coverSemigroup.measure_univ ht, data.coverSemigroup.measure_ne_zero ht⟩

include data in
/-- The twist element is central, as required by Sengupta's source formula. -/
theorem exact_central_twist (element : CoverGroup) :
    bundleClass * element = element * bundleClass :=
  data.bundleClass_central element

include data in
/-- Hostile total-area probe: per-simplex allocations may change, but the source total may not. -/
theorem changed_region_total_area_blocked (region : Region)
    (changed : coarse.regionArea region ≠ fine.regionArea region) : False :=
  changed (data.regionArea_coherence region)

/-- Hostile surjectivity probe: no coarse face may be dropped by the candidate refinement. -/
theorem dropped_coarse_face_blocked
    (coarseFace : CoarseFace)
    (dropped : ¬∃ fineFace, data.fineFaceToCoarse fineFace = coarseFace) : False :=
  dropped (data.exists_fineFace coarseFace)

include data in
/-- Hostile ordinary Fact 2 probe. -/
theorem changed_ordinary_subdivision_factor_blocked
    (region : Region) (external : Edge → CoverGroup)
    (changed : senguptaTriangulatedRegionFactor coarse coverDensity region external ≠
      senguptaTriangulatedRegionFactor fine coverDensity region external) : False :=
  changed (data.ordinaryFactor_eq region external)

include data in
/-- Hostile fixed-twist Fact 2 probe. -/
theorem changed_twisted_subdivision_factor_blocked
    (region : Region) (external : Edge → CoverGroup)
    (changed : senguptaTriangulatedTwistedRegionFactor coarse coverDensity
        bundleClass region external ≠
      senguptaTriangulatedTwistedRegionFactor fine coverDensity
        bundleClass region external) : False :=
  changed (data.twistedFactor_eq region external)

end

end YangMills.Dimensions.TwoDimensionalSenguptaSubdivisionFactorInvariance.Probes
