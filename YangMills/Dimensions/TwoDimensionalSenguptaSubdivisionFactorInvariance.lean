/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.TwoDimensionalSenguptaTriangulatedHeatFactors

/-!
# One-step Sengupta subdivision factor invariance

This file isolates the factor-level content needed for Sengupta Definition 7.6, Fact 2, for one
coarse/fine finite-face candidate pair on one exact normalized compact-Haar density semigroup and one
central twist element. Fine faces map surjectively to coarse faces and stay in the same region, while
only the source-required total area of each region is fixed. Fact 1 permits simplex-area
redistribution and Fact 0 removes distinguished-face dependence. The ordinary and fixed-twist boundary-conditioned factors are then required to agree for every external field.

This is an uninhabited comparison interface. It does not prove that the candidate words form an
embedded simplicial subdivision or claim the universal quantification over every source-valid
subdivision required by the full Fact 2.
-/

namespace YangMills.Dimensions

open MeasureTheory
open YangMills.Mathematics
open scoped ENNReal BigOperators

noncomputable section

universe uCover uEdge uCoarseInternal uCoarseFace uFineInternal uFineFace uRegion

variable
    {CoverGroup : Type uCover} [Group CoverGroup]
    [TopologicalSpace CoverGroup] [IsTopologicalGroup CoverGroup]
    [CompactSpace CoverGroup] [MeasurableSpace CoverGroup] [BorelSpace CoverGroup]
    {Edge : Type uEdge}
    {CoarseInternal : Type uCoarseInternal} [Fintype CoarseInternal]
    {CoarseFace : Type uCoarseFace} [Fintype CoarseFace] [DecidableEq CoarseFace]
    {FineInternal : Type uFineInternal} [Fintype FineInternal]
    {FineFace : Type uFineFace} [Fintype FineFace] [DecidableEq FineFace]
    {Region : Type uRegion} [DecidableEq Region]
    {coverDensity : ℝ → CoverGroup → ℝ≥0∞}
    {coarse : TwoDimensionalSenguptaTriangulatedRegionData
      Edge CoarseInternal CoarseFace Region}
    {fine : TwoDimensionalSenguptaTriangulatedRegionData
      Edge FineInternal FineFace Region}
    {bundleClass : CoverGroup}

/-- Factor-level certificate for one candidate finite-face subdivision pair. -/
structure TwoDimensionalSenguptaSubdivisionFactorInvarianceData where
  coverSemigroup : NormalizedCompactHaarDensitySemigroupData coverDensity
  bundleClass_central : ∀ element, bundleClass * element = element * bundleClass
  fineFaceToCoarse : FineFace → CoarseFace
  fineFaceToCoarse_surjective : Function.Surjective fineFaceToCoarse
  faceRegion_coherence : ∀ fineFace,
    coarse.faceRegion (fineFaceToCoarse fineFace) = fine.faceRegion fineFace
  /-- Fact 2 assumes equality of total area, not a fixed per-coarse-face allocation. Fact 1 handles
  redistribution among simplices. -/
  regionArea_coherence : ∀ region, coarse.regionArea region = fine.regionArea region
  ordinaryFactor_eq : ∀ region external,
    senguptaTriangulatedRegionFactor coarse coverDensity region external =
      senguptaTriangulatedRegionFactor fine coverDensity region external
  twistedFactor_eq : ∀ region external,
    senguptaTriangulatedTwistedRegionFactor coarse coverDensity
        bundleClass region external =
      senguptaTriangulatedTwistedRegionFactor fine coverDensity
        bundleClass region external

namespace TwoDimensionalSenguptaSubdivisionFactorInvarianceData

/-- Every coarse candidate face has at least one fine face above it. -/
theorem exists_fineFace
    (data : TwoDimensionalSenguptaSubdivisionFactorInvarianceData
      (coverDensity := coverDensity) (coarse := coarse) (fine := fine)
      (bundleClass := bundleClass))
    (coarseFace : CoarseFace) :
    ∃ fineFace, data.fineFaceToCoarse fineFace = coarseFace :=
  data.fineFaceToCoarse_surjective coarseFace

end TwoDimensionalSenguptaSubdivisionFactorInvarianceData

end

end YangMills.Dimensions
