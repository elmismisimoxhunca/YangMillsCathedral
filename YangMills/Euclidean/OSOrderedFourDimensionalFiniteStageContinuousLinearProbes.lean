/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageContinuousLinear

/-!
# Hostile probes for continuous linear exact-source stage maps

The probes lock bundled maps to the exact stage extension, named algebra, support, scalar, and
nonzero source sequence. They do not infer global topological-vector-space structure.
-/

namespace YangMills.OSOrderedFourDimensionalFiniteStageContinuousLinear.Probes

noncomputable section

noncomputable local instance osSourceSpaceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance osSourceSpaceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance osSourceSequenceTopologyForProbes :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology

noncomputable local instance osSourceSequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance osSourceSequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The continuous linear map is exactly the previously defined stage map. -/
theorem exact_stage_map
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x =
      osPositiveTimeOrderedFourDimensionalStageToSequence s x :=
  rfl

/-- Complex-linearity uses the exact named source-sequence addition. -/
theorem exact_stage_addition
    (s : Finset PositiveArity)
    (x y : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s (x + y) =
      @Add.add _ osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup.toAdd
        (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x)
        (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s y) :=
  map_add (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s) x y

/-- Complex-linearity uses the exact named source-sequence scalar action. -/
theorem exact_stage_scalar_action
    (s : Finset PositiveArity) (c : ℂ)
    (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s (c • x) =
      @SMul.smul ℂ _ osPositiveTimeOrderedFourDimensionalSequenceModule.toSMul c
        (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x) :=
  map_smul (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s) c x

/-- Bundling cannot detach output support from the selected finite stage. -/
theorem exact_support_bound
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x).support ⊆ s :=
  osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap_support_subset s x

/-- The continuous linear stage map is genuinely continuous for the named final topology. -/
theorem exact_continuity (s : Finset PositiveArity) :
    Continuous (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s) :=
  (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s).continuous

/-- The actual-support stage of the nonzero singleton is sent back to that exact sequence, so the
continuous linear map cannot be a zero map. -/
theorem nonzero_singleton_stage_retained :
    osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence.support
      (osPositiveTimeOrderedFourDimensionalSequenceToSupportStage
        singletonPositiveTimeBumpFourDimensionalOSSourceSequence) =
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence := by
  rw [osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap_apply]
  exact osPositiveTimeOrderedFourDimensionalStage_recover
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence

end

end YangMills.OSOrderedFourDimensionalFiniteStageContinuousLinear.Probes
