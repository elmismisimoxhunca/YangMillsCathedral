/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerCoordinateContinuityCriterion
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for the linear coordinate continuity criterion

The probes expose finite-stage coordinate decomposition, both implications of the criterion,
arity-zero and positive-arity specialization, and rejection of a globally continuous linear map
whose coordinate composite is discontinuous.
-/

namespace YangMills.Euclidean.SchwingerCoordinateContinuityCriterion.Probes

noncomputable local instance scalarFiniteSchwartzProbeTopologyLocal
    (d : EuclideanDimension) : TopologicalSpace (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzFiniteStageFinalTopology d

noncomputable local instance scalarFiniteSchwartzProbeAddCommGroupLocal
    (d : EuclideanDimension) : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceAddCommGroup d

noncomputable local instance scalarFiniteSchwartzProbeModuleLocal
    (d : EuclideanDimension) : Module ℂ (ScalarFiniteSchwartzSequence d) :=
  scalarFiniteSchwartzSequenceModule d

/-- Every stage is exactly the finite sum of all its coordinate injections. -/
theorem exact_stage_coordinate_sum
    (d : EuclideanDimension) (s : Finset ℕ) (x : ScalarFiniteSchwartzStage d s) :
    scalarFiniteSchwartzStageToSequence d s x =
      ∑ q : {n // n ∈ s},
        scalarSchwartzCoordinateInjectionContinuousLinearMap d q.val (x q) :=
  scalarFiniteSchwartzStage_coordinate_decomposition d s x

/-- Component extraction cannot silently discard a summand of a finite sequence sum. -/
theorem exact_component_of_finite_sum
    (d : EuclideanDimension) {α : Type*} [DecidableEq α]
    (u : Finset α) (F : α → ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (∑ a ∈ u, F a).component n = ∑ a ∈ u, (F a).component n :=
  scalarFiniteSchwartzSequence_finset_sum_component d u F n

/-- Global continuity forces continuity after every exact coordinate injection. -/
theorem global_continuity_forces_every_coordinate
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y) (hL : Continuous L)
    (n : ℕ) :
    Continuous (fun f : ScalarSchwartzTestFunction d n =>
      L (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f)) :=
  (continuous_linearMap_from_scalarFiniteSchwartzSequence_iff_coordinates d L).mp hL n

/-- Continuity of every coordinate composite forces global continuity for the named preliminary
finite-stage topology. -/
theorem every_coordinate_forces_global_continuity
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y)
    (h : ∀ n : ℕ, Continuous (fun f : ScalarSchwartzTestFunction d n =>
      L (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f))) :
    Continuous L :=
  (continuous_linearMap_from_scalarFiniteSchwartzSequence_iff_coordinates d L).mpr h

/-- The criterion includes the normalized zero-arity coordinate rather than starting at arity one. -/
theorem global_continuity_includes_zero_arity
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y) (hL : Continuous L) :
    Continuous (fun f : ScalarSchwartzTestFunction d 0 =>
      L (scalarSchwartzCoordinateInjectionContinuousLinearMap d 0 f)) :=
  global_continuity_forces_every_coordinate d L hL 0

/-- The criterion also reaches the arity-one space containing the explicit nonzero bump. -/
theorem global_continuity_includes_bump_arity
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y) (hL : Continuous L) :
    Continuous (fun f : ScalarSchwartzTestFunction d 1 =>
      L (scalarSchwartzCoordinateInjectionContinuousLinearMap d 1 f)) :=
  global_continuity_forces_every_coordinate d L hL 1

/-- A purported globally continuous linear map cannot have even one discontinuous coordinate
composite. -/
theorem discontinuous_coordinate_blocks_global_continuity
    (d : EuclideanDimension) {Y : Type*}
    [TopologicalSpace Y] [AddCommGroup Y] [Module ℂ Y] [ContinuousAdd Y]
    (L : ScalarFiniteSchwartzSequence d →ₗ[ℂ] Y) (n : ℕ)
    (hbad : ¬Continuous (fun f : ScalarSchwartzTestFunction d n =>
      L (scalarSchwartzCoordinateInjectionContinuousLinearMap d n f)))
    (hglobal : Continuous L) : False :=
  hbad (global_continuity_forces_every_coordinate d L hglobal n)

/-- The explicit singleton bump's support stage decomposes through coordinate injections without
losing its nonzero arity-one component. -/
theorem bump_stage_coordinate_sum_retains_one
    (d : EuclideanDimension) :
    (∑ q : {n // n ∈
        (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support},
      scalarSchwartzCoordinateInjectionContinuousLinearMap d q.val
        (scalarFiniteSchwartzSequenceToSupportStage d
          (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence q)).component 1 =
      positiveTimeBumpSchwartz d := by
  rw [← scalarFiniteSchwartzStage_coordinate_decomposition]
  rw [scalarFiniteSchwartzStage_recover]
  exact MathlibStrictPositiveTimeTestSequence.extendedComponent_positive
    (singletonPositiveTimeBumpSequence d) PositiveArity.one

end YangMills.Euclidean.SchwingerCoordinateContinuityCriterion.Probes
