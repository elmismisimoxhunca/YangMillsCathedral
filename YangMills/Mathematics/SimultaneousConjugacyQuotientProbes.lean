/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SimultaneousConjugacyQuotient

/-!
# Hostile probes for simultaneous conjugacy quotients
-/

namespace YangMills.Mathematics.SimultaneousConjugacyQuotient.Probes

universe uIndex uG

/-- Equality requires one common conjugator for every coordinate, not a coordinate-dependent family. -/
theorem exact_common_conjugator
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) :
    simultaneousConjugacyClass family₁ = simultaneousConjugacyClass family₂ ↔
      ∃ conjugator : G, ∀ index,
        family₂ index = conjugator⁻¹ * family₁ index * conjugator :=
  simultaneousConjugacyClass_eq_iff family₁ family₂

/-- A common diagonal conjugation preserves the exact family class. -/
theorem exact_diagonal_invariance
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) (conjugator : G) :
    simultaneousConjugacyClass
        (fun index => conjugator⁻¹ * family index * conjugator) =
      simultaneousConjugacyClass family :=
  simultaneousConjugacyClass_conjugate family conjugator

/-- The quotient projection is continuous for the exact quotient topology. -/
theorem exact_projection_continuous
    {Index : Type uIndex} {G : Type uG} [Group G] [TopologicalSpace G] :
    Continuous (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyClass_continuous

/-- The same projection is a genuine topological quotient map, not only a surjection. -/
theorem exact_projection_isQuotientMap
    {Index : Type uIndex} {G : Type uG} [Group G] [TopologicalSpace G] :
    Topology.IsQuotientMap (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyClass_isQuotientMap

/-- Finite simultaneous quotients of compact groups retain compactness. -/
theorem exact_finite_compact_quotient
    {Index : Type uIndex} {G : Type uG} [Group G] [TopologicalSpace G]
    [Fintype Index] [CompactSpace G] :
    IsCompact (Set.univ : Set (SimultaneousConjugacyQuotient Index G)) :=
  simultaneousConjugacyQuotient_isCompact_univ

/-- Proper diagonal conjugation makes every finite compact-Hausdorff quotient Hausdorff. -/
theorem exact_finite_quotient_hausdorff
    {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] :
    T2Space (SimultaneousConjugacyQuotient Index G) :=
  inferInstance

/-- Open orbit projection retains second countability for finite families. -/
theorem exact_finite_quotient_secondCountable
    {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] :
    SecondCountableTopology (SimultaneousConjugacyQuotient Index G) :=
  inferInstance

/-- Compact Hausdorff second-countable finite quotients are Polish in their genuine quotient
topology. -/
theorem exact_finite_quotient_polish
    {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] :
    PolishSpace (SimultaneousConjugacyQuotient Index G) :=
  inferInstance

/-- Under compact-Polish source hypotheses, the exact final measurable quotient equals the Borel
space of the same genuine quotient topology. -/
theorem exact_finite_quotient_measurable_eq_borel
    {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] :
    (inferInstance : MeasurableSpace (SimultaneousConjugacyQuotient Index G)) =
      borel (SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyQuotient_measurableSpace_eq_borel

/-- The same quotient is a genuine standard Borel space, so regular conditional-kernel existence
APIs can use it without an unrelated measurable presentation. -/
theorem exact_finite_quotient_standardBorel
    {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] :
    StandardBorelSpace (SimultaneousConjugacyQuotient Index G) :=
  inferInstance

/-- The quotient projection is measurable for its exact final measurable space. -/
theorem exact_projection_measurable
    {Index : Type uIndex} {G : Type uG} [Group G] [MeasurableSpace G] :
    Measurable (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyClass_measurable

/-- Coordinatewise conjugacy does not imply simultaneous conjugacy. Any supplied family pair with
coordinatewise witnesses but no common witness has distinct simultaneous classes, even though every
one-coordinate class agrees. -/
theorem coordinatewise_substitution_blocked
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G)
    (coordinatewise : ∀ index, ∃ conjugator : G,
      family₂ index = conjugator⁻¹ * family₁ index * conjugator)
    (noCommon : ¬ ∃ conjugator : G, ∀ index,
      family₂ index = conjugator⁻¹ * family₁ index * conjugator) :
    simultaneousConjugacyClass family₁ ≠ simultaneousConjugacyClass family₂ ∧
      ∀ index,
        simultaneousConjugacyClass (fun _ : Unit => family₁ index) =
          simultaneousConjugacyClass (fun _ : Unit => family₂ index) := by
  constructor
  · intro equality
    exact noCommon ((simultaneousConjugacyClass_eq_iff family₁ family₂).mp equality)
  · intro index
    obtain ⟨conjugator, equality⟩ := coordinatewise index
    apply (simultaneousConjugacyClass_eq_iff _ _).mpr
    exact ⟨conjugator, fun _ => equality⟩

/-- An empty family has no holonomy information and its simultaneous quotient is subsingleton. A
source-facing finite-family observation layer must separately prevent empty-family vacuity where the
source requires a genuine loop observation. -/
theorem empty_index_quotient_subsingleton
    (G : Type uG) [Group G] :
    Subsingleton (SimultaneousConjugacyQuotient Empty G) := by
  constructor
  intro first second
  refine Quotient.inductionOn₂ first second ?_
  intro family₁ family₂
  apply (simultaneousConjugacyClass_eq_iff _ _).mpr
  refine ⟨1, ?_⟩
  intro index
  exact index.elim

end YangMills.Mathematics.SimultaneousConjugacyQuotient.Probes
