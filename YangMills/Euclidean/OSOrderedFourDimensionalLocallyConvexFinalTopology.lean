/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalFiniteStageLocallyConvex
import YangMills.Euclidean.OSOrderedFourDimensionalSequenceFinalTopologyCompatibility

/-!
# A locally convex final topology for exact OS source sequences

The raw finite-stage final topology need not automatically preserve binary products, so its joint
addition remains open. This module constructs instead the categorical locally convex final
candidate: the `sInf` of all topologies that make the named source-sequence algebra a topological
complex module, make it locally convex over `ℝ`, and make every exact finite-stage extension
continuous. Mathlib's lattice theorems prove that this `sInf` has all those properties.

This topology is kept distinct from the previously constructed raw finite-stage final topology. The
raw topology is compared to it, and equality is characterized exactly by admissibility of the raw
topology. We do not identify this construction with OS-I's printed Hausdorff locally convex direct
sum, prove the two topologies equal, construct a completion or completed tensor product, state
`(E2)`, supply OS-II growth, or perform reconstruction.
-/

namespace YangMills

noncomputable section

noncomputable local instance sourceAddCommGroupForLocallyConvexFinal
    (arity : PositiveArity) :
    AddCommGroup (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.addCommGroup arity

noncomputable local instance sourceModuleForLocallyConvexFinal
    (arity : PositiveArity) :
    Module ℂ (OSPositiveTimeOrderedFourDimensionalSourceSpace arity) :=
  OSPositiveTimeOrderedFourDimensionalSourceSpace.module arity

noncomputable local instance sequenceAddCommGroupForLocallyConvexFinal :
    AddCommGroup OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceAddCommGroup

noncomputable local instance sequenceModuleForLocallyConvexFinal :
    Module ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
  osPositiveTimeOrderedFourDimensionalSequenceModule

/-- A topology is admissible for the locally convex final construction when it makes the exact
sequence algebra a topological complex module, is real locally convex, and makes every exact
finite-stage extension continuous. Hausdorff separation is deliberately not hidden in this
predicate. -/
def IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    (t : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence) : Prop :=
  @ContinuousAdd OSPositiveTimeOrderedFourDimensionalTestSequence t inferInstance ∧
  @ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence
    inferInstance inferInstance t ∧
  @LocallyConvexSpace ℝ OSPositiveTimeOrderedFourDimensionalTestSequence
    inferInstance inferInstance inferInstance inferInstance t ∧
  ∀ s : Finset PositiveArity,
    @Continuous (OSPositiveTimeOrderedFourDimensionalStage s)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance t
      (osPositiveTimeOrderedFourDimensionalStageToSequence s)

/-- Finest topology, in Mathlib's reversed topology order, among all admissible locally convex
final topologies on exact source sequences. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  sInf {t | IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology t}

/-- Named joint continuity of addition for the locally convex final topology. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousAdd :
    @ContinuousAdd OSPositiveTimeOrderedFourDimensionalTestSequence
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance :=
  continuousAdd_sInf fun _ ht => ht.1

/-- Named joint continuity of complex scalar multiplication for the locally convex final topology. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousSMul :
    @ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence
      inferInstance inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  continuousSMul_sInf fun _ ht => ht.2.1

/-- Named real local convexity for the locally convex final topology. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalLocallyConvexSpace :
    @LocallyConvexSpace ℝ OSPositiveTimeOrderedFourDimensionalTestSequence
      inferInstance inferInstance inferInstance inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  LocallyConvexSpace.sInf fun _ ht => ht.2.2.1

/-- Every exact finite-stage extension is continuous into the locally convex final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal
    (s : Finset PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalStage s)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      (osPositiveTimeOrderedFourDimensionalStageToSequence s) := by
  rw [continuous_iff_coinduced_le]
  apply le_sInf
  intro t ht
  exact continuous_iff_coinduced_le.mp (ht.2.2.2 s)

/-- The locally convex final topology is itself admissible, so the defining family is nonempty and
the construction is not a vacuous lattice artifact. -/
theorem isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_self :
    IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology :=
  ⟨osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousAdd,
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousSMul,
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalLocallyConvexSpace,
    continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal⟩

/-- Exact universal minimality in Mathlib's topology order. -/
theorem osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le
    (t : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence)
    (ht : IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology t) :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology ≤ t :=
  sInf_le ht

/-- The raw finite-stage final topology lies below the locally convex final topology in Mathlib's
reversed topology order because all exact stage maps remain continuous. -/
theorem osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology_le_locallyConvexFinal :
    osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology ≤
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology := by
  unfold osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology
  apply iSup_le
  intro s
  exact continuous_iff_coinduced_le.mp
    (continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal s)

/-- The locally convex and raw final topologies agree exactly when the raw topology already has all
admissibility properties. This is the explicit comparison gate, not an asserted equality. -/
theorem osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_eq_raw_iff :
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology =
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology ↔
      IsOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology := by
  constructor
  · intro h
    rw [← h]
    exact isOSPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_self
  · intro hraw
    apply le_antisymm
    · exact osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology_le _ hraw
    · exact osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology_le_locallyConvexFinal

/-- Every exact stage extension bundles as a continuous complex-linear map into the locally convex
final source topology. -/
def osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap
    (s : Finset PositiveArity) :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    OSPositiveTimeOrderedFourDimensionalStage s →L[ℂ]
      OSPositiveTimeOrderedFourDimensionalTestSequence := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  exact { osPositiveTimeOrderedFourDimensionalStageToSequenceLinearMap s with
    cont := continuous_osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinal s }

/-- Bundling into the locally convex final topology preserves the exact stage extension. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap_apply
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
    osPositiveTimeOrderedFourDimensionalStageToLocallyConvexFinalContinuousLinearMap s x =
      osPositiveTimeOrderedFourDimensionalStageToSequence s x :=
  rfl

/-- Negation is continuous for the locally convex final topology because it is multiplication by
`-1`. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_neg :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence
      OSPositiveTimeOrderedFourDimensionalTestSequence
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
      (fun f => -f) := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  letI : ContinuousSMul ℂ OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousSMul
  have h := continuous_smul.comp
    ((continuous_const : Continuous
      (fun _ : OSPositiveTimeOrderedFourDimensionalTestSequence => (-1 : ℂ))).prodMk
        continuous_id)
  change Continuous (fun f : OSPositiveTimeOrderedFourDimensionalTestSequence =>
    (-1 : ℂ) • f) at h
  simpa only [neg_one_smul] using h

/-- Named continuous negation for the locally convex final topology. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousNeg :
    @ContinuousNeg OSPositiveTimeOrderedFourDimensionalTestSequence
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  exact ⟨continuous_osPositiveTimeOrderedFourDimensionalLocallyConvexFinal_neg⟩

/-- Named topological additive-group structure for the locally convex final topology. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalLocallyConvexFinalIsTopologicalAddGroup :
    @IsTopologicalAddGroup OSPositiveTimeOrderedFourDimensionalTestSequence
      osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology inferInstance := by
  letI : TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalTopology
  letI : ContinuousAdd OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousAdd
  letI : ContinuousNeg OSPositiveTimeOrderedFourDimensionalTestSequence :=
    osPositiveTimeOrderedFourDimensionalLocallyConvexFinalContinuousNeg
  exact { }

end

end YangMills
