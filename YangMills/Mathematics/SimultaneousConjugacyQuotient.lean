/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Simultaneous conjugacy quotients

Finite families of gauge holonomies transform by one common conjugation. Their gauge-invariant value
is therefore a simultaneous (diagonal) conjugacy class, not a tuple of unrelated one-coordinate
conjugacy classes. This file packages the exact quotient and its final measurable space.

No compact group, probability law, or Yang--Mills object is constructed here. Under supplied compact
Hausdorff/second-countable/Polish group hypotheses, the quotient topology and its Borel compatibility
are derived.
-/

namespace YangMills.Mathematics

universe uIndex uG

/-- Two `G`-valued families are simultaneously conjugate when one common group element conjugates
every coordinate. -/
def SimultaneouslyConjugate {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) : Prop :=
  ∃ conjugator : G, ∀ index, family₂ index = conjugator⁻¹ * family₁ index * conjugator

/-- The genuine left action by diagonal conjugation. Its standard orientation is
`g • family = g family g⁻¹`; this has the same orbits as the source convention
`family₂ = c⁻¹ family₁ c`. -/
@[reducible] def diagonalConjugationMulAction
    (Index : Type uIndex) (G : Type uG) [Group G] : MulAction G (Index → G) where
  smul conjugator family index := conjugator * family index * conjugator⁻¹
  one_smul family := by
    show (fun index => (1 : G) * family index * (1 : G)⁻¹) = family
    funext index
    simp
  mul_smul first second family := by
    show (fun index => (first * second) * family index * (first * second)⁻¹) =
      (fun index => first * (second * family index * second⁻¹) * first⁻¹)
    funext index
    simp [mul_assoc]

/-- Orbit relation of the exact diagonal conjugation action. -/
@[reducible] def diagonalConjugationOrbitRel
    (Index : Type uIndex) (G : Type uG) [Group G] : Setoid (Index → G) := by
  let action := diagonalConjugationMulAction Index G
  letI : SMul G (Index → G) := action.toSMul
  letI : MulAction G (Index → G) := action
  exact MulAction.orbitRel G (Index → G)

/-- Simultaneous conjugacy as Mathlib's exact orbit equivalence relation. -/
@[reducible] def simultaneousConjugacySetoid
    (Index : Type uIndex) (G : Type uG) [Group G] : Setoid (Index → G) :=
  diagonalConjugationOrbitRel Index G

/-- The orbit relation is exactly the displayed common-conjugator formula. -/
theorem simultaneousConjugacySetoid_apply
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) :
    simultaneousConjugacySetoid Index G family₁ family₂ ↔
      SimultaneouslyConjugate family₁ family₂ := by
  let action := diagonalConjugationMulAction Index G
  letI : SMul G (Index → G) := action.toSMul
  letI : MulAction G (Index → G) := action
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨conjugator, equality⟩
    refine ⟨conjugator, ?_⟩
    intro index
    change (fun index => conjugator * family₂ index * conjugator⁻¹) = family₁ at equality
    have coordinateEquality := congrFun equality index
    rw [← coordinateEquality]
    simp [mul_assoc]
  · rintro ⟨conjugator, equality⟩
    refine ⟨conjugator, ?_⟩
    change (fun index => conjugator * family₂ index * conjugator⁻¹) = family₁
    funext index
    rw [equality index]
    simp [mul_assoc]

/-- Exact quotient of an indexed family by one common diagonal conjugation. -/
@[reducible] def SimultaneousConjugacyQuotient (Index : Type uIndex) (G : Type uG) [Group G] :
    Type (max uIndex uG) :=
  Quotient (simultaneousConjugacySetoid Index G)

/-- Canonical simultaneous-conjugacy class of a family. -/
def simultaneousConjugacyClass {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) : SimultaneousConjugacyQuotient Index G :=
  Quotient.mk (simultaneousConjugacySetoid Index G) family

/-- Every simultaneous class has an exact family representative. -/
theorem simultaneousConjugacyClass_surjective
    {Index : Type uIndex} {G : Type uG} [Group G] :
    Function.Surjective (simultaneousConjugacyClass :
      (Index → G) → SimultaneousConjugacyQuotient Index G) :=
  Quotient.mk_surjective

/-- Equality of classes is exactly conjugation of every coordinate by one common element. -/
theorem simultaneousConjugacyClass_eq_iff
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family₁ family₂ : Index → G) :
    simultaneousConjugacyClass family₁ = simultaneousConjugacyClass family₂ ↔
      ∃ conjugator : G, ∀ index,
        family₂ index = conjugator⁻¹ * family₁ index * conjugator := by
  constructor
  · intro equality
    exact (simultaneousConjugacySetoid_apply family₁ family₂).mp (Quotient.exact equality)
  · intro relation
    apply Quotient.sound
    exact (simultaneousConjugacySetoid_apply family₁ family₂).mpr relation

/-- One common conjugation leaves the exact simultaneous class unchanged. -/
theorem simultaneousConjugacyClass_conjugate
    {Index : Type uIndex} {G : Type uG} [Group G]
    (family : Index → G) (conjugator : G) :
    simultaneousConjugacyClass
        (fun index => conjugator⁻¹ * family index * conjugator) =
      simultaneousConjugacyClass family := by
  apply (simultaneousConjugacyClass_eq_iff _ _).mpr
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

/-- A finite simultaneous-conjugacy quotient of a compact Hausdorff topological group is Hausdorff.
The proof uses the genuine continuous proper diagonal action, not a supplied separation witness. -/
noncomputable instance simultaneousConjugacyQuotientT2Space
    [Fintype Index] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] :
    T2Space (SimultaneousConjugacyQuotient Index G) := by
  let action := diagonalConjugationMulAction Index G
  letI : SMul G (Index → G) := action.toSMul
  letI : MulAction G (Index → G) := action
  letI : ContinuousSMul G (Index → G) := ⟨by
    change Continuous fun pair : G × (Index → G) =>
      fun index => pair.1 * pair.2 index * pair.1⁻¹
    fun_prop⟩
  letI : ProperSMul G (Index → G) := ⟨by
    apply Continuous.isProperMap
    exact continuous_smul.prodMk continuous_snd⟩
  infer_instance

/-- A finite simultaneous quotient retains second countability from the group. The diagonal orbit
projection is open because each fixed conjugation is a homeomorphism. -/
noncomputable instance simultaneousConjugacyQuotientSecondCountableTopology
    [Fintype Index] [IsTopologicalGroup G] [SecondCountableTopology G] :
    SecondCountableTopology (SimultaneousConjugacyQuotient Index G) := by
  let action := diagonalConjugationMulAction Index G
  letI : SMul G (Index → G) := action.toSMul
  letI : MulAction G (Index → G) := action
  letI : ContinuousConstSMul G (Index → G) := ⟨fun conjugator => by
    change Continuous fun family : Index → G =>
      fun index => conjugator * family index * conjugator⁻¹
    fun_prop⟩
  exact ContinuousConstSMul.secondCountableTopology

/-- Compact Hausdorff second-countable simultaneous quotients are Polish. Urysohn metrization gives
an exact compatible metric, and compactness makes that metric complete. -/
noncomputable instance simultaneousConjugacyQuotientPolishSpace
    [Fintype Index] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [SecondCountableTopology G] :
    PolishSpace (SimultaneousConjugacyQuotient Index G) := by
  letI : MetricSpace (SimultaneousConjugacyQuotient Index G) :=
    TopologicalSpace.metrizableSpaceMetric (SimultaneousConjugacyQuotient Index G)
  exact PolishSpace.mk

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

section Borel

variable {Index : Type uIndex} {G : Type uG} [Fintype Index] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

/-- For a finite family over a compact Polish topological group, the final measurable quotient is
exactly the Borel measurable space of the genuine quotient topology. -/
theorem simultaneousConjugacyQuotient_measurableSpace_eq_borel :
    (inferInstance : MeasurableSpace (SimultaneousConjugacyQuotient Index G)) =
      borel (SimultaneousConjugacyQuotient Index G) := by
  change MeasurableSpace.map
    (simultaneousConjugacyClass : (Index → G) → SimultaneousConjugacyQuotient Index G)
      inferInstance = _
  exact simultaneousConjugacyClass_continuous.map_eq_borel
    simultaneousConjugacyClass_surjective

/-- The exact final measurable space is therefore packaged as the Borel space of the quotient
topology under the same compact-Polish hypotheses. Together with the derived quotient Polish
instance, this also yields Mathlib's `StandardBorelSpace` automatically. -/
noncomputable instance simultaneousConjugacyQuotientBorelSpace :
    BorelSpace (SimultaneousConjugacyQuotient Index G) where
  measurable_eq := simultaneousConjugacyQuotient_measurableSpace_eq_borel

end Borel

end YangMills.Mathematics
