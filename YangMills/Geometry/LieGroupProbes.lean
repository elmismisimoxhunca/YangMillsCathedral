/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Geometry.LieGroup

/-!
# Hostile probes for compact-simple gauge groups

The certificate's type already requires a finite-dimensional Hausdorff second-countable smooth real
manifold and smooth group operations. These contradiction probes isolate the remaining record
fields and the bridge to the tangent Lie algebra.
-/

namespace YangMills.Geometry.Probes

open Set
open scoped Manifold ContDiff

universe u v

variable
    {G : Type v} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- Removing compactness would allow a certified noncompact carrier. -/
theorem noncompact_gaugeGroup_blocked
    (data : CompactSimpleGaugeGroupData G E)
    (noncompact : ¬IsCompact (Set.univ : Set G)) : False :=
  noncompact data.compact

/-- Lie-algebra simplicity alone must not allow a disconnected global group. -/
theorem disconnected_gaugeGroup_blocked
    (data : CompactSimpleGaugeGroupData G E)
    (disconnected : ¬IsConnected (Set.univ : Set G)) : False :=
  disconnected data.connected

/-- Explicit carrier anti-vacuity rejects a subsingleton group. -/
theorem subsingleton_gaugeGroup_blocked [Subsingleton G]
    (data : CompactSimpleGaugeGroupData G E) : False :=
  not_nontrivial G data.nontrivial

/-- An abelian tangent bracket cannot be hidden behind the word “simple.” -/
theorem abelian_groupLieAlgebra_blocked
    (data : CompactSimpleGaugeGroupData G E)
    (abelian : HasAbelianGroupLieAlgebra G E) : False :=
  hasSimpleGroupLieAlgebra_not_abelian data.simple_lieAlgebra abelian

/-- A proper nonzero tangent Lie ideal is incompatible with the certificate. -/
theorem proper_nonzero_groupLieIdeal_blocked
    (data : CompactSimpleGaugeGroupData G E)
    (properIdeal : HasProperNonzeroGroupLieIdeal G E) : False :=
  hasSimpleGroupLieAlgebra_noProperNonzeroIdeal data.simple_lieAlgebra properIdeal

end YangMills.Geometry.Probes
