/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.TopologicalPrincipalBundle

/-!
# Hostile probes for topological principal bundles

The probes isolate continuity, atlas coverage and membership, local source/target shape, and local
equivariance. Smoothness is intentionally absent.
-/

namespace YangMills.Geometry.Probes

open Set

universe uG uB uP

variable {G : Type uG} {B : Type uB} {P : Type uP}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace B] [TopologicalSpace P]
variable {torsor : PrincipalBundleTorsorData G B P}

/-- A discontinuous projection cannot be certified. -/
theorem discontinuous_projection_blocked
    (bundle : TopologicalPrincipalBundleData torsor)
    (discontinuous : ¬Continuous torsor.projection) : False :=
  discontinuous bundle.projection_continuous

/-- A discontinuous uncurried right action cannot be certified. -/
theorem discontinuous_rightAction_blocked
    (bundle : TopologicalPrincipalBundleData torsor)
    (discontinuous : ¬Continuous fun pg : P × G => torsor.rightAction pg.1 pg.2) : False :=
  discontinuous bundle.rightAction_continuous

/-- The selected chart cannot miss the base point it is supposed to cover. -/
theorem uncovered_basePoint_blocked
    (bundle : TopologicalPrincipalBundleData torsor) (b : B)
    (misses : b ∉ (bundle.trivializationAt b).baseSet) : False :=
  misses (bundle.mem_baseSet_trivializationAt b)

/-- A selected chart cannot be disconnected from the designated atlas. -/
theorem selected_chart_outside_atlas_blocked
    (bundle : TopologicalPrincipalBundleData torsor) (b : B)
    (outside : bundle.trivializationAt b ∉ bundle.trivializationAtlas) : False :=
  outside (bundle.trivializationAt_mem_atlas b)

omit [IsTopologicalGroup G] in
/-- A local trivialization source cannot differ from the inverse image of its base set. -/
theorem malformed_trivialization_source_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (malformed : chart.toPartialHomeomorph.source ≠ torsor.projection ⁻¹' chart.baseSet) : False :=
  malformed chart.source_eq

omit [IsTopologicalGroup G] in
/-- A local trivialization target cannot differ from `baseSet × G`. -/
theorem malformed_trivialization_target_blocked
    (chart : PrincipalBundleLocalTrivialization torsor)
    (malformed : chart.toPartialHomeomorph.target ≠
      chart.baseSet ×ˢ (Set.univ : Set G)) : False :=
  malformed chart.target_eq

omit [IsTopologicalGroup G] in
/-- A local chart cannot violate its declared right-action coordinate law. -/
theorem nonequivariant_localTrivialization_blocked
    (chart : PrincipalBundleLocalTrivialization torsor) (p : P)
    (memSource : p ∈ chart.toPartialHomeomorph.source) (g : G)
    (mismatch : chart.toPartialHomeomorph (torsor.rightAction p g) ≠
      ((chart.toPartialHomeomorph p).1, (chart.toPartialHomeomorph p).2 * g)) : False :=
  mismatch (chart.rightAction_coordinate p memSource g)

/-- The designated atlas contains a chart covering every total-space point. -/
theorem designated_atlas_covers
    (bundle : TopologicalPrincipalBundleData torsor) (p : P) :
    ∃ chart, chart ∈ bundle.trivializationAtlas ∧
      p ∈ chart.toPartialHomeomorph.source :=
  bundle.exists_atlas_trivialization_mem_source p

/-- The selected charts really cover every total-space point. -/
theorem selected_trivializations_cover
    (bundle : TopologicalPrincipalBundleData torsor) (p : P) :
    p ∈ ⋃ b : B, (bundle.trivializationAt b).toPartialHomeomorph.source :=
  Set.mem_iUnion.mpr ⟨torsor.projection p, bundle.mem_source_trivializationAt p⟩

/-- The trivial product bundle is positive consistency evidence for the full topological interface. -/
theorem trivial_topologicalPrincipalBundle_exists
    (G : Type uG) (B : Type uB)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace B] :
    Nonempty (TopologicalPrincipalBundleData (PrincipalBundleTorsorData.trivial G B)) :=
  ⟨TopologicalPrincipalBundleData.trivial G B⟩

end YangMills.Geometry.Probes
