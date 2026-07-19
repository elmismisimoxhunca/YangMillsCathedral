/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalTestSequence

/-!
# Finite-stage final topology for exact four-dimensional OS source sequences

For every finite set of positive arities, this module forms the product of the separate scalar
`f₀ ∈ ℂ` with the corresponding exact positive-arity OS-I source spaces, extends absent components
by zero, and maps into the exact-support source-sequence carrier. Every sequence is recovered from
its actual support stage. The supremum of the resulting coinduced topologies is packaged with its
exact finite-stage universal property.

This is deliberately named a **finite-stage final topology**. Although it is the expected
construction underlying a locally convex direct sum, this module does not yet install compatible
complex-module/topological-vector-space structures or prove equality with OS-I's printed locally
convex direct-sum topology. It also does not construct the distinct completed positive-half-space
tensor product, a product/involution on this source carrier, `(E2)`, OS-II growth, or reconstruction.
-/

namespace YangMills

noncomputable section

/-- Product of the separate scalar component with exact source spaces at a finite set of positive
arities. -/
abbrev OSPositiveTimeOrderedFourDimensionalStage (s : Finset PositiveArity) :=
  ℂ × ((arity : {a // a ∈ s}) →
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity.val)

/-- Extend finite-stage positive components by the exact zero source test outside the stage. -/
def osPositiveTimeOrderedFourDimensionalStageComponent
    (s : Finset PositiveArity)
    (x : OSPositiveTimeOrderedFourDimensionalStage s) (arity : PositiveArity) :
    OSPositiveTimeOrderedFourDimensionalSourceSpace arity := by
  classical
  by_cases h : arity ∈ s
  · exact x.2 ⟨arity, h⟩
  · exact zeroOSPositiveTimeOrderedFourDimensionalSourceTest arity

/-- Map finite-stage data into the exact-support source sequence, filtering zero entries rather than
retaining a disconnected support superset. -/
def osPositiveTimeOrderedFourDimensionalStageToSequence
    (s : Finset PositiveArity)
    (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    OSPositiveTimeOrderedFourDimensionalTestSequence := by
  classical
  exact {
    zeroPoint := x.1
    support := s.filter (fun arity =>
      (osPositiveTimeOrderedFourDimensionalStageComponent s x arity).toSchwartz ≠ 0)
    component := osPositiveTimeOrderedFourDimensionalStageComponent s x
    mem_support_iff := by
      intro arity
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hnonzero
        refine ⟨?_, hnonzero⟩
        by_contra hnot
        apply hnonzero
        simp [osPositiveTimeOrderedFourDimensionalStageComponent, hnot,
          zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
          OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz] }

/-- The stage map preserves the designated scalar component exactly. -/
@[simp]
theorem osPositiveTimeOrderedFourDimensionalStageToSequence_zeroPoint
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalStageToSequence s x).zeroPoint = x.1 :=
  rfl

/-- The stage map's exact positive support cannot escape the selected finite stage. -/
theorem osPositiveTimeOrderedFourDimensionalStageToSequence_support_subset
    (s : Finset PositiveArity) (x : OSPositiveTimeOrderedFourDimensionalStage s) :
    (osPositiveTimeOrderedFourDimensionalStageToSequence s x).support ⊆ s := by
  classical
  intro arity h
  exact (Finset.mem_filter.mp h).1

/-- Restrict an exact source sequence to the product stage indexed by its actual positive support. -/
def osPositiveTimeOrderedFourDimensionalSequenceToSupportStage
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    OSPositiveTimeOrderedFourDimensionalStage f.support :=
  ⟨f.zeroPoint, fun arity => f.component arity.val⟩

/-- Extensionality from the separate scalar and all underlying positive Schwartz components. -/
@[ext]
theorem OSPositiveTimeOrderedFourDimensionalTestSequence.ext
    {f g : OSPositiveTimeOrderedFourDimensionalTestSequence}
    (hzero : f.zeroPoint = g.zeroPoint)
    (hcomponent : ∀ arity,
      (f.component arity).toSchwartz = (g.component arity).toSchwartz) :
    f = g := by
  have hsupport : f.support = g.support := by
    ext arity
    rw [f.mem_support_iff, g.mem_support_iff, hcomponent arity]
  cases f with
  | mk fzero fsupport fcomponent fmem =>
    cases g with
    | mk gzero gsupport gcomponent gmem =>
      simp only at hzero hsupport hcomponent
      subst gzero
      subst gsupport
      have components_equal : fcomponent = gcomponent := by
        funext arity
        apply Subtype.ext
        exact hcomponent arity
      subst gcomponent
      rfl

/-- Every exact source sequence is recovered from the finite stage given by its actual positive
support, including its independent scalar component. -/
theorem osPositiveTimeOrderedFourDimensionalStage_recover
    (f : OSPositiveTimeOrderedFourDimensionalTestSequence) :
    osPositiveTimeOrderedFourDimensionalStageToSequence f.support
      (osPositiveTimeOrderedFourDimensionalSequenceToSupportStage f) = f := by
  apply OSPositiveTimeOrderedFourDimensionalTestSequence.ext
  · rfl
  · intro arity
    by_cases h : arity ∈ f.support
    · simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
        osPositiveTimeOrderedFourDimensionalStageComponent, h,
        osPositiveTimeOrderedFourDimensionalSequenceToSupportStage]
    · rw [show (f.component arity).toSchwartz = 0 from
        f.component_toSchwartz_eq_zero_of_not_mem arity h]
      simp [osPositiveTimeOrderedFourDimensionalStageToSequence,
        osPositiveTimeOrderedFourDimensionalStageComponent, h,
        zeroOSPositiveTimeOrderedFourDimensionalSourceTest,
        OSPositiveTimeOrderedFourDimensionalSourceSpace.toSchwartz]

/-- Named final topology generated by all exact finite positive-arity stage maps. It is reducible
only for local topology-lattice proofs and is not installed globally. -/
@[reducible]
noncomputable def osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology :
    TopologicalSpace OSPositiveTimeOrderedFourDimensionalTestSequence :=
  ⨆ s : Finset PositiveArity, TopologicalSpace.coinduced
    (osPositiveTimeOrderedFourDimensionalStageToSequence s) inferInstance

/-- Every exact finite-stage map is continuous into the named final topology. -/
theorem continuous_osPositiveTimeOrderedFourDimensionalStageToSequence
    (s : Finset PositiveArity) :
    @Continuous (OSPositiveTimeOrderedFourDimensionalStage s)
      OSPositiveTimeOrderedFourDimensionalTestSequence inferInstance
      osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology
      (osPositiveTimeOrderedFourDimensionalStageToSequence s) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun t : Finset PositiveArity =>
    TopologicalSpace.coinduced
      (osPositiveTimeOrderedFourDimensionalStageToSequence t) inferInstance) s

/-- Exact universal property: a map out of the source sequence is continuous for the named topology
iff its composite with every finite-stage map is continuous. -/
theorem continuous_from_osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology_iff
    {Y : Type*} [TopologicalSpace Y]
    (g : OSPositiveTimeOrderedFourDimensionalTestSequence → Y) :
    @Continuous OSPositiveTimeOrderedFourDimensionalTestSequence Y
        osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology inferInstance g ↔
      ∀ s : Finset PositiveArity,
        Continuous (g ∘ osPositiveTimeOrderedFourDimensionalStageToSequence s) := by
  unfold osPositiveTimeOrderedFourDimensionalFiniteStageFinalTopology
  rw [continuous_iSup_dom]
  apply forall_congr'
  intro s
  exact continuous_coinduced_dom

end

end YangMills
