/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalUniversal

/-!
# Hostile probes for the locally convex final universal property

The probes expose both directions of the stagewise criterion, recover the independently constructed
all-coordinate CLM from stagewise continuity, retain its nonzero singleton value, and enforce
uniqueness of continuity packaging.
-/

namespace YangMills.OSOrderedFourDimensionalLocallyConvexFinalUniversal.Probes

noncomputable section

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceTopologicalAddGroupForProbes (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.isTopologicalAddGroup arity

noncomputable local instance sourceContinuousSMulForProbes (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sourceLocallyConvexForProbes (arity : PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.locallyConvexSpace arity

noncomputable local instance sequenceTopologyForProbes :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology

noncomputable local instance sequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The exact linear continuity criterion quantifies over every finite stage. -/
theorem exact_stagewise_continuity_criterion
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y) :
    Continuous L ↔ ∀ s : Finset PositiveArity,
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s) :=
  continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_iff L

/-- The independently constructed all-coordinate map is continuous on every exact finite stage. -/
theorem allCoordinates_stagewise_continuous (s : Finset PositiveArity) :
    Continuous
      (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap ∘
        osPositiveTimeOrderedFourDimensionalStageToSequence s) :=
  continuous_osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinates.comp
    (continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal s)

/-- Stagewise universal packaging recovers the exact independently constructed all-coordinate CLM. -/
theorem exact_allCoordinates_stagewise_package :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
        osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap
        allCoordinates_stagewise_continuous =
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  rfl

/-- Universal packaging cannot erase the explicit nonzero singleton coordinate. -/
theorem nonzero_singleton_value_retained :
    ((osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap
      allCoordinates_stagewise_continuous
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence).2
        PositiveArity.one).toSchwartz ≠ 0 := by
  change (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
    PositiveArity.one).toSchwartz ≠ 0
  rw [singletonPositiveTimeBumpFourDimensionalOSSourceSequence,
    MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component,
    singletonPositiveTimeBumpSequence_component_one]
  exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four

/-- Two proofs of all-stage continuity cannot produce disconnected continuous-linear maps. -/
theorem exact_stagewise_package_uniqueness
    (h : ∀ s : Finset PositiveArity,
      Continuous
        (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap ∘
          osPositiveTimeOrderedFourDimensionalStageToSequence s)) :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
        osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap h =
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
        osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap
        allCoordinates_stagewise_continuous :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise_unique
    _ _ _

end

end YangMills.OSOrderedFourDimensionalLocallyConvexFinalUniversal.Probes
