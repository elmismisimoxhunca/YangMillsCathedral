/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalSequenceFinalTopologyCompatibility

/-!
# Hostile probes for exact-source final-topology compatibility

These probes exercise the quotient presentation, joint scalar action, negation, finite-union
addition, separate addition continuity, and the explicit product-quotient condition still required
for joint addition. They intentionally do not install `ContinuousAdd`.
-/

namespace YangMills.OSOrderedFourDimensionalSequenceFinalTopologyCompatibility.Probes

noncomputable section

noncomputable local instance sourceAddCommGroupForProbes (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForProbes (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceContinuousAddForProbes (arity : PositiveArity) :
    ContinuousAdd (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousAdd arity

noncomputable local instance sourceContinuousSMulForProbes (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sequenceTopologyForProbes :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology

noncomputable local instance sequenceAddCommGroupForProbes :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForProbes :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- The total-stage presentation is a genuine quotient map, not merely a continuous surjection. -/
theorem exact_total_stage_quotient :
    Topology.IsQuotientMap osPositiveTimeOrderedFourDimensionalTotalStageToSequence :=
  osPositiveTimeOrderedFourDimensionalTotalStageToSequence_isQuotientMap

/-- The quotient presentation recovers every sequence from its actual support stage. -/
theorem exact_support_stage_recovery
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    osPositiveTimeOrderedFourDimensionalTotalStageToSequence
      ⟨f.support, osPositiveTimeOrderedFourDimensionalSequenceToSupportStage f⟩ = f :=
  osPositiveTimeOrderedFourDimensionalStage_recover f

/-- Installing the named sequence scalar structure yields the exact jointly continuous action. -/
theorem exact_named_continuous_scalar_action :
    letI : ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalSequenceContinuousSMul
    Continuous (fun p : ℂ × OSPositiveTimeOrderedFourDimensionalTestSequence => p.1 • p.2) := by
  letI : ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalSequenceContinuousSMul
  exact continuous_smul

/-- The scalar action retains the explicit nonzero singleton exactly at scalar one. -/
theorem nonzero_singleton_scalar_identity :
    (1 : ℂ) • singletonPositiveTimeBumpFourDimensionalOSSourceSequence =
      singletonPositiveTimeBumpFourDimensionalOSSourceSequence :=
  one_smul ℂ singletonPositiveTimeBumpFourDimensionalOSSourceSequence

/-- The explicit singleton remains nonzero under the installed algebra. -/
theorem nonzero_singleton_retained :
    singletonPositiveTimeBumpFourDimensionalOSSourceSequence ≠ 0 := by
  intro h
  have hcomponent := congrArg
    (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence =>
      (f.component ⟨1, Nat.succ_pos 0⟩).toSchwartz) h
  rw [osPositiveTimeOrderedFourDimensionalSequence_instance_zero_component] at hcomponent
  have hnonzero :
      (singletonPositiveTimeBumpFourDimensionalOSSourceSequence.component
        PositiveArity.one).toSchwartz ≠ 0 := by
    rw [singletonPositiveTimeBumpFourDimensionalOSSourceSequence,
      MathlibStrictPositiveTimeTestSequence.toFourDimensionalOSSourceSequence_component,
      singletonPositiveTimeBumpSequence_component_one]
    exact positiveTimeBumpSchwartz_ne_zero EuclideanDimension.four
  exact hnonzero hcomponent

/-- Installing named sequence negation proves continuity without pretending addition is jointly
continuous. -/
theorem exact_named_continuous_negation :
    letI : ContinuousNeg OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalSequenceContinuousNeg
    Continuous (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence => -f) := by
  letI : ContinuousNeg OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalSequenceContinuousNeg
  exact continuous_neg

/-- Stage-pair addition lands in the exact union stage and factors to named sequence addition. -/
theorem exact_union_stage_addition
    (s t : Finset PositiveArity)
    (p : OSPositiveTimeOrderedFourDimensionalStage s ×
      OSPositiveTimeOrderedFourDimensionalStage t) :
    osPositiveTimeOrderedFourDimensionalStageToSequence (s ∪ t)
        (osPositiveTimeOrderedFourDimensionalStagePairAdd s t p) =
      osPositiveTimeOrderedFourDimensionalStageToSequence s p.1 +
        osPositiveTimeOrderedFourDimensionalStageToSequence t p.2 :=
  osPositiveTimeOrderedFourDimensionalStagePairAdd_factor s t p

/-- Addition is continuous in the right sequence variable separately. -/
theorem exact_separate_addition_right
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    Continuous (fun g : OSPositiveTimeOrderedFourDimensionalTestSequence => f + g) :=
  continuous_osPositiveTimeOrderedFourDimensionalSequence_add_left f

/-- Joint addition is exposed only under the exact missing product-quotient hypothesis. -/
theorem conditional_joint_addition
    (hproduct : Topology.IsQuotientMap
      (Prod.map osPositiveTimeOrderedFourDimensionalTotalStageToSequence
        osPositiveTimeOrderedFourDimensionalTotalStageToSequence)) :
    Continuous (fun p : OSPositiveTimeOrderedFourDimensionalTestSequence ×
      OSPositiveTimeOrderedFourDimensionalTestSequence => p.1 + p.2) :=
  continuous_osPositiveTimeOrderedFourDimensionalSequence_add_of_product_isQuotientMap hproduct

end

end YangMills.OSOrderedFourDimensionalSequenceFinalTopologyCompatibility.Probes
