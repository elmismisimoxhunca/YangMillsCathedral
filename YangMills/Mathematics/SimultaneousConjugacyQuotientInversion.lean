/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SimultaneousConjugacyQuotient
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Inversion on simultaneous-conjugacy quotients

Pointwise group inversion is compatible with one common diagonal conjugator and therefore descends
to the exact simultaneous-conjugacy quotient. This file constructs that descended involution and
proves its topological and measurable regularity. It supplies the precise `t ↦ t⁻¹` operation needed
when the same boundary circle is viewed with opposite orientation.
-/

namespace YangMills.Mathematics

noncomputable section

universe uIndex uG

/-- Pointwise inversion descends to simultaneous-conjugacy classes. -/
def simultaneousConjugacyInverse {Index : Type uIndex} {G : Type uG} [Group G] :
    SimultaneousConjugacyQuotient Index G → SimultaneousConjugacyQuotient Index G :=
  Quotient.map (fun family index => (family index)⁻¹) (by
    intro first second related
    apply (simultaneousConjugacySetoid_apply _ _).mpr
    obtain ⟨conjugator, equality⟩ :=
      (simultaneousConjugacySetoid_apply _ _).mp related
    refine ⟨conjugator, ?_⟩
    intro index
    change (second index)⁻¹ = conjugator⁻¹ * (first index)⁻¹ * conjugator
    rw [equality index]
    simp [mul_assoc])

/-- Inversion of an exact class is the class of the pointwise inverse family. -/
theorem simultaneousConjugacyInverse_class
    {Index : Type uIndex} {G : Type uG} [Group G] (family : Index → G) :
    simultaneousConjugacyInverse (simultaneousConjugacyClass family) =
      simultaneousConjugacyClass (fun index => (family index)⁻¹) :=
  rfl

/-- The descended inversion is involutive. -/
theorem simultaneousConjugacyInverse_involutive
    {Index : Type uIndex} {G : Type uG} [Group G] :
    Function.Involutive
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) := by
  intro conjugacyClass
  refine Quotient.inductionOn conjugacyClass ?_
  intro family
  change simultaneousConjugacyClass (fun index => ((family index)⁻¹)⁻¹) =
    simultaneousConjugacyClass family
  congr 1
  funext index
  simp

/-- The descended inversion is bijective. -/
theorem simultaneousConjugacyInverse_bijective
    {Index : Type uIndex} {G : Type uG} [Group G] :
    Function.Bijective
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) :=
  simultaneousConjugacyInverse_involutive.bijective

section Topology

variable {Index : Type uIndex} {G : Type uG} [TopologicalSpace G]
    [Group G] [ContinuousInv G]

/-- Inversion is continuous for the genuine quotient topology. -/
theorem simultaneousConjugacyInverse_continuous :
    Continuous
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) := by
  apply simultaneousConjugacyClass_isQuotientMap.continuous_iff.mpr
  rw [show simultaneousConjugacyInverse ∘ simultaneousConjugacyClass =
      simultaneousConjugacyClass ∘ (fun family : Index → G => fun index => (family index)⁻¹) by
    funext family
    exact simultaneousConjugacyInverse_class family]
  apply simultaneousConjugacyClass_continuous.comp
  fun_prop

end Topology

section Measurability

variable {Index : Type uIndex} {G : Type uG} [Group G] [MeasurableSpace G]
    [MeasurableInv G]

/-- Inversion is measurable for the final measurable quotient, independently of any topology. -/
theorem simultaneousConjugacyInverse_measurable :
    Measurable
      (simultaneousConjugacyInverse : SimultaneousConjugacyQuotient Index G →
        SimultaneousConjugacyQuotient Index G) := by
  intro measurableSet measurableSet_target
  change MeasurableSet
    (simultaneousConjugacyClass ⁻¹'
      (simultaneousConjugacyInverse ⁻¹' measurableSet))
  have sourcePreimage : MeasurableSet (simultaneousConjugacyClass ⁻¹' measurableSet) :=
    measurableSet_target
  have pointwiseInverseMeasurable : Measurable (fun family : Index → G =>
      fun index => (family index)⁻¹) := by
    fun_prop
  have inversePreimage := pointwiseInverseMeasurable sourcePreimage
  simpa only [Set.preimage_preimage, Function.comp_def,
    simultaneousConjugacyInverse_class] using inversePreimage

end Measurability

end

end YangMills.Mathematics
