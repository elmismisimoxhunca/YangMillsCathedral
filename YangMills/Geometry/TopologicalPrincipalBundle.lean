/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.PrincipalBundleTorsor
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Topological principal bundles

This module adds an equivariant local-triviality atlas and continuity to the fiberwise torsor core.
It still does not claim smoothness, connections, or curvature.
-/

namespace YangMills.Geometry

open Set

universe uG uB uP

variable {G : Type uG} {B : Type uB} {P : Type uP}
variable [Group G] [TopologicalSpace G] [TopologicalSpace B] [TopologicalSpace P]

/-- An equivariant topological trivialization of a principal torsor over an open base set. -/
structure PrincipalBundleLocalTrivialization
    (torsor : PrincipalBundleTorsorData G B P) where
  /-- The underlying local homeomorphism from total space to base times group. -/
  toPartialHomeomorph : OpenPartialHomeomorph P (B × G)
  /-- Open set in the base over which this chart trivializes the bundle. -/
  baseSet : Set B
  isOpen_baseSet : IsOpen baseSet
  /-- The chart source is exactly the inverse image of the base set. -/
  source_eq : toPartialHomeomorph.source = torsor.projection ⁻¹' baseSet
  /-- The chart target is exactly `baseSet × G`. -/
  target_eq : toPartialHomeomorph.target = baseSet ×ˢ (Set.univ : Set G)
  /-- The first chart coordinate is the bundle projection. -/
  base_coordinate : ∀ p ∈ toPartialHomeomorph.source,
    (toPartialHomeomorph p).1 = torsor.projection p
  /-- The second chart coordinate intertwines the right action with right multiplication. -/
  rightAction_coordinate : ∀ p ∈ toPartialHomeomorph.source, ∀ g,
    toPartialHomeomorph (torsor.rightAction p g) =
      ((toPartialHomeomorph p).1, (toPartialHomeomorph p).2 * g)

namespace PrincipalBundleLocalTrivialization

variable {torsor : PrincipalBundleTorsorData G B P}

instance : CoeFun (PrincipalBundleLocalTrivialization torsor) fun _ => P → B × G :=
  ⟨fun trivialization => trivialization.toPartialHomeomorph⟩

/-- Right action preserves the source of an equivariant local trivialization. -/
theorem rightAction_mem_source (trivialization : PrincipalBundleLocalTrivialization torsor)
    {p : P} (memSource : p ∈ trivialization.toPartialHomeomorph.source) (g : G) :
    torsor.rightAction p g ∈ trivialization.toPartialHomeomorph.source := by
  rw [trivialization.source_eq] at memSource ⊢
  simpa only [mem_preimage, torsor.projection_rightAction] using memSource

end PrincipalBundleLocalTrivialization

/-- A topological principal bundle built over a fixed fiberwise torsor.

The selected trivialization at every base point witnesses coverage; the atlas remains explicit for
future transition-function and smoothness conditions. -/
structure TopologicalPrincipalBundleData
    (torsor : PrincipalBundleTorsorData G B P) [IsTopologicalGroup G] where
  /-- The projection is continuous. -/
  projection_continuous : Continuous torsor.projection
  /-- The uncurried right action is continuous. -/
  rightAction_continuous : Continuous fun pg : P × G => torsor.rightAction pg.1 pg.2
  /-- Designated atlas of equivariant local trivializations. -/
  trivializationAtlas : Set (PrincipalBundleLocalTrivialization torsor)
  /-- A selected trivialization around each base point. -/
  trivializationAt : B → PrincipalBundleLocalTrivialization torsor
  /-- The selected chart really covers its base point. -/
  mem_baseSet_trivializationAt : ∀ b, b ∈ (trivializationAt b).baseSet
  /-- Every selected chart belongs to the designated atlas. -/
  trivializationAt_mem_atlas : ∀ b, trivializationAt b ∈ trivializationAtlas

namespace TopologicalPrincipalBundleData

variable [IsTopologicalGroup G]
variable {torsor : PrincipalBundleTorsorData G B P}

/-- Every total-space point lies in the source of the chart selected at its projection. -/
theorem mem_source_trivializationAt (bundle : TopologicalPrincipalBundleData torsor) (p : P) :
    p ∈ (bundle.trivializationAt (torsor.projection p)).toPartialHomeomorph.source := by
  rw [(bundle.trivializationAt (torsor.projection p)).source_eq]
  exact bundle.mem_baseSet_trivializationAt (torsor.projection p)

/-- Every total-space point is covered by a chart belonging to the designated atlas. -/
theorem exists_atlas_trivialization_mem_source
    (bundle : TopologicalPrincipalBundleData torsor) (p : P) :
    ∃ chart, chart ∈ bundle.trivializationAtlas ∧
      p ∈ chart.toPartialHomeomorph.source :=
  ⟨bundle.trivializationAt (torsor.projection p),
    bundle.trivializationAt_mem_atlas (torsor.projection p),
    bundle.mem_source_trivializationAt p⟩

/-- The selected local trivializations cover the entire total carrier. -/
theorem source_iUnion_eq_univ (bundle : TopologicalPrincipalBundleData torsor) :
    ⋃ b : B, (bundle.trivializationAt b).toPartialHomeomorph.source = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact Set.mem_iUnion.mpr ⟨torsor.projection p, bundle.mem_source_trivializationAt p⟩

/-- A locally trivial principal-bundle projection is an open map. -/
theorem projection_isOpenMap (bundle : TopologicalPrincipalBundleData torsor) :
    IsOpenMap torsor.projection := by
  classical
  apply IsOpenMap.of_sections
  intro p
  let chart := bundle.trivializationAt (torsor.projection p)
  let coordinate : G := (chart.toPartialHomeomorph p).2
  let fallback : B → P := fun b => Classical.choose (torsor.fiber_nonempty b)
  let localSection : B → P := fun b => if b ∈ chart.baseSet then
    chart.toPartialHomeomorph.symm (b, coordinate) else fallback b
  have p_mem_source : p ∈ chart.toPartialHomeomorph.source :=
    bundle.mem_source_trivializationAt p
  have projection_p_mem : torsor.projection p ∈ chart.baseSet :=
    bundle.mem_baseSet_trivializationAt (torsor.projection p)
  have pair_mem_target (b : B) (hb : b ∈ chart.baseSet) :
      (b, coordinate) ∈ chart.toPartialHomeomorph.target := by
    rw [chart.target_eq]
    exact ⟨hb, Set.mem_univ coordinate⟩
  refine ⟨localSection, ?_, ?_, ?_⟩
  · have inverse_continuousAt : ContinuousAt chart.toPartialHomeomorph.symm
        (torsor.projection p, coordinate) :=
      chart.toPartialHomeomorph.continuousOn_symm.continuousAt
        (chart.toPartialHomeomorph.open_target.mem_nhds
          (pair_mem_target (torsor.projection p) projection_p_mem))
    have pair_continuous : ContinuousAt (fun b : B => (b, coordinate))
        (torsor.projection p) :=
      continuousAt_id.prodMk continuousAt_const
    have local_continuous : ContinuousAt
        (fun b : B => chart.toPartialHomeomorph.symm (b, coordinate))
        (torsor.projection p) := by
      simpa [Function.comp_def] using
        inverse_continuousAt.comp_of_eq pair_continuous rfl
    apply local_continuous.congr_of_eventuallyEq
    filter_upwards [chart.isOpen_baseSet.mem_nhds projection_p_mem] with b hb
    simp only [localSection, hb, if_true]
  · simp only [localSection, projection_p_mem, if_true]
    have pair_eq : (torsor.projection p, coordinate) = chart.toPartialHomeomorph p := by
      apply Prod.ext
      · exact (chart.base_coordinate p p_mem_source).symm
      · rfl
    rw [pair_eq]
    exact chart.toPartialHomeomorph.left_inv p_mem_source
  · intro b
    by_cases hb : b ∈ chart.baseSet
    · simp only [localSection, hb, if_true]
      have inverse_mem_source := chart.toPartialHomeomorph.map_target (pair_mem_target b hb)
      calc
        torsor.projection (chart.toPartialHomeomorph.symm (b, coordinate)) =
            (chart.toPartialHomeomorph (chart.toPartialHomeomorph.symm (b, coordinate))).1 :=
          (chart.base_coordinate _ inverse_mem_source).symm
        _ = b := by rw [chart.toPartialHomeomorph.right_inv (pair_mem_target b hb)]
    · simp only [localSection, hb, if_false, fallback]
      exact Classical.choose_spec (torsor.fiber_nonempty b)

/-- A locally trivial principal-bundle projection is an open quotient map. -/
theorem projection_isOpenQuotientMap (bundle : TopologicalPrincipalBundleData torsor) :
    IsOpenQuotientMap torsor.projection :=
  ⟨torsor.projection_surjective, bundle.projection_continuous, bundle.projection_isOpenMap⟩

/-- In particular, the base topology is the quotient topology induced by the projection. -/
theorem projection_isQuotientMap (bundle : TopologicalPrincipalBundleData torsor) :
    Topology.IsQuotientMap torsor.projection :=
  bundle.projection_isOpenQuotientMap.isQuotientMap

/-- The global product torsor carries the expected topological principal-bundle structure. -/
def trivial (G : Type uG) (B : Type uB)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace B] :
    TopologicalPrincipalBundleData (PrincipalBundleTorsorData.trivial G B) := by
  let chart : PrincipalBundleLocalTrivialization (PrincipalBundleTorsorData.trivial G B) := {
    toPartialHomeomorph := OpenPartialHomeomorph.refl (B × G)
    baseSet := Set.univ
    isOpen_baseSet := isOpen_univ
    source_eq := by simp
    target_eq := by simp
    base_coordinate := by intro p _; rfl
    rightAction_coordinate := by intro p _ g; rfl
  }
  exact {
    projection_continuous := continuous_fst
    rightAction_continuous :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd)
    trivializationAtlas := {chart}
    trivializationAt := fun _ => chart
    mem_baseSet_trivializationAt := by intro; trivial
    trivializationAt_mem_atlas := by intro; simp
  }

end TopologicalPrincipalBundleData

end YangMills.Geometry
