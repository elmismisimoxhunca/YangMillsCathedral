/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalHausdorff

/-!
# Universal property of the locally convex OS source topology

OS-I, printed p. 87, defines finite source sequences with the direct-sum topology and states its
characteristic continuity property for linear maps into a convex space. This module proves the
finite-stage form of that universal property: a complex-linear map from exact source sequences into
any real-locally-convex topological complex module is continuous exactly when its composite with
every exact finite-stage extension is continuous.

The reverse implication equips the source carrier with the topology induced by the proposed linear
map, proves that topology admissible, and invokes the universal minimality of the locally convex
final topology. This does not yet replace OS-I's natural-coordinate injections by finite-stage maps
or identify the construction with the paper's printed direct-sum topology; that exact coordinate
criterion remains a separate bridge obligation.
-/

namespace YangMills

noncomputable section

noncomputable local instance sourceAddCommGroupForLocallyConvexUniversal
    (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForLocallyConvexUniversal
    (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sequenceAddCommGroupForLocallyConvexUniversal :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForLocallyConvexUniversal :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- Finite-stage universal property for complex-linear maps out of the exact locally convex final
source topology. -/
theorem continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_iff
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y) :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence Y
        osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance L ↔
      ∀ s : Finset PositiveArity,
        Continuous (L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s) := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  constructor
  · intro h s
    exact h.comp
      (continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal s)
  · intro h
    let inducedTopology : TopologicalSpace
        OSPositiveTimeOrderedFourDimensionalTestSequence :=
      TopologicalSpace.induced L inferInstance
    have hinduced : IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
        inducedTopology := by
      refine ⟨continuousAdd_induced L, continuousSMul_induced L, ?_, ?_⟩
      · exact LocallyConvexSpace.induced (L.restrictScalars ℝ)
      · intro s
        rw [continuous_induced_rng]
        exact h s
    rw [continuous_iff_le_induced]
    exact osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le
      inducedTopology hinduced

/-- Package a stagewise-continuous complex-linear map as a continuous complex-linear map from the
locally convex final source topology. -/
def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y)
    (hL : ∀ s : Finset PositiveArity,
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s)) :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    OSPositiveTimeOrderedFourDimensionalTestSequence →L[ℂ] Y := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  exact { L with
    cont :=
      (continuous_linearMap_from_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_iff L).mpr
        hL }

/-- Stagewise packaging preserves the exact underlying linear-map value. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise_apply
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y)
    (hL : ∀ s : Finset PositiveArity,
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s))
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise
      L hL f = L f :=
  rfl

/-- Any two stagewise packages of the same algebraic linear map are equal; continuity proofs cannot
select disconnected maps. -/
theorem osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise_unique
    {Y : Type*} [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y]
    [ContinuousAdd Y] [ContinuousSMul ℂ Y] [LocallyConvexSpace ℝ Y]
    (L : OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ] Y)
    (h₁ h₂ : ∀ s : Finset PositiveArity,
      Continuous (L ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s)) :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise L h₁ =
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousLinearMapOfStagewise L h₂ := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  ext f
  rfl

end

end YangMills
