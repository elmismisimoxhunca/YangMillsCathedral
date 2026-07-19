/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexDirectSum

/-!
# Hostile probes for the exact OS locally convex direct sum

The probes lock the separate scalar and positive natural injections, exact finite-stage
recomposition, their genuine continuity, the printed coordinatewise universal property, and the
explicit nonzero source coordinate. They do not equate this topology with the raw final topology or
the distinct completed tensor product.
-/

namespace YangMills.OSOrderedFourDimensionalLocallyConvexDirectSum.Probes

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

noncomputable local instance sequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The scalar injection cannot be replaced by a positive-arity component. -/
theorem exact_scalar_natural_injection (c : ℂ) (arity : PositiveArity) :
    (osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c).zeroPoint = c ∧
    ((osPositiveTimeOrderedFourDimensionalScalarNaturalInjection c).component
      arity).toSchwartz = 0 :=
  ⟨rfl, rfl⟩

/-- Every positive-arity injection has scalar zero and recovers exactly its injected source test. -/
theorem exact_source_natural_injection (arity : PositiveArity)
    (f : OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :
    (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f).zeroPoint = 0 ∧
    (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity f).component arity = f :=
  ⟨rfl, osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_component_same arity f⟩

/-- Every selected finite stage is exactly the finite sum of the scalar and source injections. -/
theorem exact_finite_stage_recomposition
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    osPositiveTimeOrderedFourDimensionalStageToSequence s x =
      osPositiveTimeOrderedFourDimensionalScalarNaturalInjection x.1 +
        ∑ arity : {a // a ∈ s},
          osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity.val (x.2 arity) :=
  osPositiveTimeOrderedFourDimensionalStageToSequence_eq_sum_naturalInjections s x

/-- The scalar natural injection is genuinely continuous for the source-facing direct-sum topology. -/
theorem exact_scalar_injection_continuity :
    @Continuous ℂ OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexDirectSumTopology
      osPositiveTimeOrderedFourDimensionalScalarNaturalInjection :=
  continuous_osPositiveTimeOrderedFourDimensionalScalarNaturalInjection

/-- Every positive-arity natural injection is genuinely continuous. -/
theorem exact_source_injection_continuity (arity : PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalSourceSpace arity)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexDirectSumTopology
      (osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity) :=
  continuous_osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity

/-- Exact OS-I coordinatewise direct-sum continuity criterion. -/
theorem exact_natural_injection_continuity_criterion
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y) :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence Y
        osPositiveTimeOrderedFourDimensionalLocallyConvexDirectSumTopology inferInstance L ↔
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalScalarNaturalInjection) ∧
      ∀ arity : PositiveArity,
        Continuous (L ∘ osPositiveTimeOrderedFourDimensionalSourceNaturalInjection arity) :=
  continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalDirectSum_iff L

/-- The explicit nonzero source test survives its natural injection exactly. -/
theorem nonzero_source_injection_retained :
    ((osPositiveTimeOrderedFourDimensionalSourceNaturalInjection PositiveArity.one
      OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump).component
        PositiveArity.one).toSchwartz ≠ 0 := by
  rw [osPositiveTimeOrderedFourDimensionalSourceNaturalInjection_component_same]
  exact OSPositiveTimeOrderedFourDimensionalSourceSpace.positiveTimeBump_toSchwartz_ne_zero

/-- The source-facing direct-sum topology is exactly the constructed locally convex final topology,
not a silent replacement by the raw final topology. -/
theorem exact_source_topology_selection :
    osPositiveTimeOrderedFourDimensionalLocallyConvexDirectSumTopology =
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  rfl

end

end YangMills.OSOrderedFourDimensionalLocallyConvexDirectSum.Probes
