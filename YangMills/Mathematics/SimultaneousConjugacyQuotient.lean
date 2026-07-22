/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
# Simultaneous conjugacy quotients

Finite families of gauge holonomies transform by one common conjugation. Their gauge-invariant value
is therefore a simultaneous (diagonal) conjugacy class, not a tuple of unrelated one-coordinate
conjugacy classes. This file packages the exact quotient and its final measurable space.

No compact group, topology, probability law, or Yang--Mills object is constructed here.
-/

namespace YangMills.Mathematics

universe uIndex uG

/-- Two `G`-valued families are simultaneously conjugate when one common group element conjugates
every coordinate. -/
def SimultaneouslyConjugate {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) : Prop :=
  ∃ conjugator : G, ∀ index, family₂ index = conjugator⁻¹ * family₁ index * conjugator

/-- Simultaneous conjugacy is an equivalence relation. -/
def simultaneousConjugacySetoid (Index : Type uIndex) (G : Type uG) [Group G] :
    Setoid (Index → G) where
  r := SimultaneouslyConjugate
  iseqv := by
    constructor
    · intro family
      exact ⟨1, by simp⟩
    · intro family₁ family₂ relation
      obtain ⟨conjugator, equality⟩ := relation
      refine ⟨conjugator⁻¹, ?_⟩
      intro index
      have := equality index
      simp only [inv_inv]
      rw [this]
      simp [mul_assoc]
    · intro family₁ family₂ family₃ relation₁₂ relation₂₃
      obtain ⟨conjugator₁₂, equality₁₂⟩ := relation₁₂
      obtain ⟨conjugator₂₃, equality₂₃⟩ := relation₂₃
      refine ⟨conjugator₁₂ * conjugator₂₃, ?_⟩
      intro index
      rw [equality₂₃ index, equality₁₂ index]
      simp [mul_assoc]

/-- Exact quotient of an indexed family by one common diagonal conjugation. -/
@[reducible] def SimultaneousConjugacyQuotient (Index : Type uIndex) (G : Type uG) [Group G] :
    Type (max uIndex uG) :=
  Quotient (simultaneousConjugacySetoid Index G)

/-- Canonical simultaneous-conjugacy class of a family. -/
def simultaneousConjugacyClass {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) : SimultaneousConjugacyQuotient Index G :=
  Quotient.mk (simultaneousConjugacySetoid Index G) family

/-- Equality of classes is exactly conjugation of every coordinate by one common element. -/
theorem simultaneousConjugacyClass_eq_iff
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) :
    simultaneousConjugacyClass family₁ = simultaneousConjugacyClass family₂ ↔
      ∃ conjugator : G, ∀ index,
        family₂ index = conjugator⁻¹ * family₁ index * conjugator := by
  constructor
  · exact Quotient.exact
  · intro relation
    apply Quotient.sound
    exact relation

/-- One common conjugation leaves the exact simultaneous class unchanged. -/
theorem simultaneousConjugacyClass_conjugate
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) (conjugator : G) :
    simultaneousConjugacyClass
        (fun index => conjugator⁻¹ * family index * conjugator) =
      simultaneousConjugacyClass family := by
  apply Quotient.sound
  exact ⟨conjugator⁻¹, by simp [mul_assoc]⟩

section Topology

variable {Index : Type uIndex} {G : Type uG} [Group G] [TopologicalSpace G]

/-- The exact simultaneous-conjugacy projection is continuous for the genuine quotient topology. -/
theorem simultaneousConjugacyClass_continuous :
    Continuous (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) := by
  exact continuous_quotient_mk'

/-- The projection onto the exact simultaneous quotient is a genuine topological quotient map. -/
theorem simultaneousConjugacyClass_isQuotientMap :
    Topology.IsQuotientMap (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) := by
  exact isQuotientMap_quotient_mk'

/-- A finite-family simultaneous quotient of a compact group is compact. -/
theorem simultaneousConjugacyQuotient_isCompact_univ
    [Fintype Index] [CompactSpace G] :
    IsCompact (Set.univ : Set (SimultaneousConjugacyQuotient Index G)) :=
  isCompact_univ

end Topology

section Measurable

variable {Index : Type uIndex} {G : Type uG} [Group G] [MeasurableSpace G]

/-- Final measurable space induced by the exact quotient projection. -/
instance simultaneousConjugacyQuotientMeasurableSpace :
    MeasurableSpace (SimultaneousConjugacyQuotient Index G) :=
  MeasurableSpace.map simultaneousConjugacyClass inferInstance

/-- The exact quotient projection is measurable by construction of the final measurable space. -/
theorem simultaneousConjugacyClass_measurable :
    Measurable (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) := by
  rw [measurable_iff_le_map]
  rfl

end Measurable

end YangMills.Mathematics
