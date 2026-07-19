/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSequenceAlgebra

/-!
# Continuous linear exact-source finite-stage maps

This module locally combines the named source-space algebra, source-sequence algebra, and exact
finite-stage final topology. It proves every generating stage map complex-linear and packages it as
a continuous complex-linear map.

This verifies compatibility of the topology with its generating linear maps only. It does not yet
prove joint sequence addition or scalar multiplication continuous, install a global topological
vector space, establish local convexity, identify OS-I's locally convex direct sum, or define
`(E2)`.
-/

namespace YangMills

noncomputable section

noncomputable local instance osSourceSpaceAddCommGroupForStage (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance osSourceSpaceModuleForStage (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance osSourceSequenceTopologyForStage :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology

noncomputable local instance osSourceSequenceAddCommGroupForStage :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance osSourceSequenceModuleForStage :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- Every exact-source finite-stage extension is complex-linear for the named source-sequence
module. -/
def osPositiveTimeOrderedFourDimensionalStageToSequenceLinearMap
    (s : Finset PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalStage s →ₗ[ℂ]
      OSPositiveTimeOrderedFourDimensionalTestSequence where
  toFun := osPositiveTimeOrderedFourDimensionalStageToSequence s
  map_add' x y := by
    apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
    · rfl
    · intro arity
      change ((osPositiveTimeOrderedFourDimensionalStageToSequence s (x + y)).component
          arity).toSchwartz =
        ((osPositiveTimeOrderedFourDimensionalStageToSequence s x).component
          arity).toSchwartz +
        ((osPositiveTimeOrderedFourDimensionalStageToSequence s y).component
          arity).toSchwartz
      by_cases h : arity ∈ s
      · simp only [osPositiveTimeOrderedFourDimensionalStageToSequence,
          osPositiveTimeOrderedFourDimensionalStageComponent, dif_pos h]
        exact OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_add_toSchwartz
          arity (x.2 ⟨arity, h⟩) (y.2 ⟨arity, h⟩)
      · simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
          osPositiveTimeOrderedFourDimensionalStageComponent, h,
          zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
          OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]
  map_smul' c x := by
    apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
    · rfl
    · intro arity
      change ((osPositiveTimeOrderedFourDimensionalStageToSequence s (c • x)).component
          arity).toSchwartz =
        c • ((osPositiveTimeOrderedFourDimensionalStageToSequence s x).component
          arity).toSchwartz
      by_cases h : arity ∈ s
      · simp only [osPositiveTimeOrderedFourDimensionalStageToSequence,
          osPositiveTimeOrderedFourDimensionalStageComponent, dif_pos h]
        exact OSPositiveTimeOrderedFourDimensionalSourceSpace.instance_smul_toSchwartz
          arity c (x.2 ⟨arity, h⟩)
      · simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
          osPositiveTimeOrderedFourDimensionalStageComponent, h,
          zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
          OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Every generating exact-source stage map is a continuous complex-linear map into the named
finite-stage final topology. -/
def osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap
    (s : Finset PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalStage s →L[ℂ]
      OSPositiveTimeOrderedFourDimensionalTestSequence :=
  { osPositiveTimeOrderedFourDimensionalStageToSequenceLinearMap s with
    cont := continuous_osPositiveTimeOrderedFourDimensionalStageToSequence s }

/-- Bundling preserves the exact underlying stage map. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap_apply
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x =
      osPositiveTimeOrderedFourDimensionalStageToSequence s x :=
  rfl

/-- Bundled stage-map output retains the exact support bound. -/
theorem osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap_support_subset
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalStageToSequenceContinuousLinearMap s x).support ⊆ s :=
  osPositiveTimeOrderedFourDimensionalStageToSequence_support_subset s x

end

end YangMills
