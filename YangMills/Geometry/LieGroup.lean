/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieAlgebraSimplicity
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Compact connected Lie groups with simple tangent Lie algebra

This module packages the project's explicit reading of “compact simple gauge group.” The carrier is
kept as a parameter so that finite central quotients and other global forms are not erased. A
certificate requires a Hausdorff, second-countable, finite-dimensional real smooth manifold, smooth
group operations, compactness, connectedness, a nontrivial carrier, and simplicity of the tangent
Lie algebra at the identity.

Connectedness is an explicit project convention, not a verbatim expansion of the Clay phrase.
Neither abstract-group simplicity nor simple connectedness is required. No concrete gauge group is
constructed here.
-/

namespace YangMills.Geometry

noncomputable section

open Set
open scoped Manifold ContDiff

universe u v

/-- The tangent Lie algebra of a smooth finite-dimensional real Lie group is simple.

The local instances make explicit the Mathlib bridge: finite-dimensional normed spaces are
complete, and a `C∞` Lie group supplies the `C^minSmoothness(ℝ, 3)` structure required by
`GroupLieAlgebra`'s bracket. -/
def HasSimpleGroupLieAlgebra
    (G : Type v) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] : Prop :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  LieAlgebra.IsSimple ℝ (GroupLieAlgebra (modelWithCornersSelf ℝ E) G)

/-- The tangent Lie algebra of a smooth finite-dimensional real Lie group is abelian.

This companion predicate exists so hostile probes can mention the same Mathlib tangent bracket
without leaking its local completeness and smoothness instances into every theorem signature. -/
def HasAbelianGroupLieAlgebra
    (G : Type v) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] : Prop :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  IsLieAbelian (GroupLieAlgebra (modelWithCornersSelf ℝ E) G)

/-- A proper nonzero ideal exists in the tangent Lie algebra. This is a mutation predicate used to
verify that the group certificate really reaches Mathlib's Lie-ideal semantics. -/
def HasProperNonzeroGroupLieIdeal
    (G : Type v) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] : Prop :=
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  ∃ ideal : LieIdeal ℝ (GroupLieAlgebra (modelWithCornersSelf ℝ E) G),
    ideal ≠ ⊥ ∧ ideal ≠ ⊤

/-- Source-facing certificate for the project's compact-simple gauge-group convention.

`G` remains explicit: this record does not replace it by a simply connected cover or restrict it to
`SU(N)`. `E` records the finite-dimensional real model space used by the smooth manifold. -/
structure CompactSimpleGaugeGroupData
    (G : Type v) (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace E G] [LieGroup (modelWithCornersSelf ℝ E) ∞ G] : Prop where
  /-- The whole gauge-group carrier is compact. -/
  compact : IsCompact (Set.univ : Set G)
  /-- Connectedness is imposed explicitly and is not inferred from Lie-algebra simplicity. -/
  connected : IsConnected (Set.univ : Set G)
  /-- Explicit carrier anti-vacuity, pending a reusable theorem deriving it from tangent data. -/
  nontrivial : Nontrivial G
  /-- “Simple” refers to the real tangent Lie algebra, never to the abstract group. -/
  simple_lieAlgebra : HasSimpleGroupLieAlgebra G E

variable
    {G : Type v} {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- A simple tangent Lie algebra cannot simultaneously be abelian. -/
theorem hasSimpleGroupLieAlgebra_not_abelian
    (simple : HasSimpleGroupLieAlgebra G E) : ¬HasAbelianGroupLieAlgebra G E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  exact simple.non_abelian

/-- A simple tangent Lie algebra has no proper nonzero Lie ideal. -/
theorem hasSimpleGroupLieAlgebra_noProperNonzeroIdeal
    (simple : HasSimpleGroupLieAlgebra G E) : ¬HasProperNonzeroGroupLieIdeal G E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : ENat.LEInfty (minSmoothness ℝ 3) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rintro ⟨ideal, nonzero, proper⟩
  exact (simple.eq_bot_or_eq_top ideal).elim nonzero proper

end

end YangMills.Geometry
