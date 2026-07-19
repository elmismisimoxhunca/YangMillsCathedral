/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalLocallyConvexFinalTopology
import YangMills.Mathematics.SchwartzHausdorff

/-!
# Hausdorff separation of the locally convex OS source topology

To prove the locally convex final topology Hausdorff, this module maps every exact source sequence
injectively to the product of its separate scalar and all positive-arity source components. The
induced coordinate topology is an admissible locally convex final topology. Universal minimality
therefore makes the coordinate map continuous from the locally convex final topology. Its product
codomain is Hausdorff, so continuous injectivity proves the source topology Hausdorff.

This proves separation for the constructed locally convex final topology. It still does not identify
that topology with the raw finite-stage final topology or OS-I's printed locally convex direct sum,
prove strict-carrier density/completion, construct the completed tensor product, state `(E2)`, or
perform reconstruction.
-/

namespace YangMills

noncomputable section

namespace OSPositiveTimeOrderedFourDimensionalSourceSpace

/-- Named Hausdorff structure on every exact positive-arity source space, transported through its
closed embedding into the now-proved Hausdorff ambient Schwartz space. -/
@[reducible]
noncomputable def t2Space (arity : PositiveArity) :
    T2Space (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) := by
  letI : T2Space (ScalarSchwartzTestFunction EuclideanDimension.four arity.value) :=
    SchwartzMap.t2Space
  exact (closedEmbedding_toSchwartz arity).isEmbedding.t2Space

end OSPositiveTimeOrderedFourDimensionalSourceSpace

noncomputable local instance sourceAddCommGroupForFinalHausdorff
    (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForFinalHausdorff
    (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sourceTopologicalAddGroupForFinalHausdorff
    (arity : PositiveArity) :
    IsTopologicalAddGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.isTopologicalAddGroup arity

noncomputable local instance sourceContinuousSMulForFinalHausdorff
    (arity : PositiveArity) :
    ContinuousSMul ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.continuousSMul arity

noncomputable local instance sourceLocallyConvexForFinalHausdorff
    (arity : PositiveArity) :
    LocallyConvexSpace ℝ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.locallyConvexSpace arity

noncomputable local instance sourceT2ForFinalHausdorff
    (arity : PositiveArity) :
    T2Space (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.t2Space arity

noncomputable local instance sequenceAddCommGroupForFinalHausdorff :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForFinalHausdorff :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- Product of the separate scalar with all positive-arity source coordinates. Finite support is
not forgotten by the source sequence; this larger product is used only as a separating codomain. -/
abbrev OSPositiveTimeOrderedFourDimensionalAllCoordinates :=
  ℂ × ((arity : PositiveArity) →
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity)

/-- Exact complex-linear map from a source sequence to all scalar and positive-arity coordinates. -/
def osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap :
    OSPositiveTimeOrderedFourDimensionalTestSequence →ₗ[ℂ]
      OSPositiveTimeOrderedFourDimensionalAllCoordinates where
  toFun f := ⟨f.zeroPoint, f.component⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The all-coordinate map preserves the separate scalar exactly. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap_fst
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap f).1 =
      f.zeroPoint :=
  rfl

/-- The all-coordinate map preserves every exact positive-arity component. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap_snd
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) (arity : PositiveArity) :
    (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap f).2 arity =
      f.component arity :=
  rfl

/-- Scalar plus all positive-arity source coordinates separate exact source sequences. -/
theorem osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap_injective :
    Function.Injective osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap := by
  intro f g h
  apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
  · exact congrArg Prod.fst h
  · intro arity
    exact congrArg
      (fun x : OSPositiveTimeOrderedFourDimensionalAllCoordinates =>
        (x.2 arity).toSchwartz) h

/-- Auxiliary topology induced by the injective map to the Hausdorff all-coordinate product. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalAllCoordinatesInducedTopology :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  TopologicalSpace.induced
    osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap inferInstance

/-- Every exact stage map is continuous into the all-coordinate induced topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStageToAllCoordinatesInduced
    (s : Finset PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalStage s)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalAllCoordinatesInducedTopology
      (osPositiveTimeOrderedFourDimensionalStageToSequence s) := by
  rw [continuous_induced_rng]
  change Continuous (fun x : OSPositiveTimeOrderedFourDimensionalStage s =>
    (x.1, fun arity =>
      osPositiveTimeOrderedFourDimensionalStageComponent s x arity))
  apply Continuous.prodMk continuous_fst
  apply continuous_pi
  intro arity
  exact continuous_osPositiveTimeOrderedFourDimensionalStageComponent s arity

/-- The separating all-coordinate induced topology is an admissible locally convex final topology. -/
theorem isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_allCoordinatesInduced :
    IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalAllCoordinatesInducedTopology := by
  refine ⟨continuousAdd_induced
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap,
    continuousSMul_induced
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap,
    ?_, continuous_osPositiveTimeOrderedFourDimensionalStageToAllCoordinatesInduced⟩
  exact LocallyConvexSpace.induced
    (osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap.restrictScalars ℝ)

/-- The locally convex final topology is finer in ordinary topology language than the separating
coordinate topology, expressed as `≤` in Mathlib's reversed topology order. -/
theorem osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le_allCoordinatesInduced :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology ≤
      osPositiveTimeOrderedFourDimensionalAllCoordinatesInducedTopology :=
  osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le _
    isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_allCoordinatesInduced

/-- The exact all-coordinate map is continuous from the locally convex final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinates :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence
      OSPositiveTimeOrderedFourDimensionalAllCoordinates
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance
      osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap := by
  rw [continuous_iff_le_induced]
  exact osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le_allCoordinatesInduced

/-- Continuous complex-linear all-coordinate map from the locally convex final source topology. -/
def osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesContinuousLinearMap :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    OSPositiveTimeOrderedFourDimensionalTestSequence →L[ℂ]
      OSPositiveTimeOrderedFourDimensionalAllCoordinates := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  exact { osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap with
    cont := continuous_osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinates }

/-- The constructed locally convex final source topology is Hausdorff. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalT2Space :
    @T2Space OSPositiveTimeOrderedFourDimensionalTestSequence
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  exact T2Space.of_injective_continuous
    osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinatesLinearMap_injective
    continuous_osPositiveTimeOrderedFourDimensionalSequenceToAllCoordinates

end

end YangMills
