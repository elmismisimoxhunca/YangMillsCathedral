/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteStageTopology

/-!
# Named complex-module structure on finite Schwinger sequences

The exact-support sequence carrier is algebraically equivalent to Mathlib's dependent finitely
supported functions. This module constructs that equivalence and transports the pointwise complex
module structure back to sequences.

The additive-group and module structures are named definitions, not global instances. Downstream
code must install them locally with `letI`. No continuity or compatibility with the preliminary
finite-stage final topology is asserted here.
-/

namespace YangMills

/-- Mathlib's dependent finitely supported-function model for natural-arity scalar Schwartz tests. -/
abbrev ScalarFiniteSchwartzDFinsupp (d : EuclideanDimension) :=
  Π₀ n : ℕ, ScalarSchwartzTestFunction d n

/-- Forget the explicit exact support proof into Mathlib's dependent finite-support carrier. -/
noncomputable def scalarFiniteSchwartzSequenceToDFinsupp
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzDFinsupp d :=
  { toFun := f.component
    support' := Trunc.mk ⟨f.support.1, fun n => by
      by_cases h : n ∈ f.support
      · exact Or.inl h
      · exact Or.inr (f.component_eq_zero_of_not_mem n h)⟩ }

@[simp] theorem scalarFiniteSchwartzSequenceToDFinsupp_apply
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    scalarFiniteSchwartzSequenceToDFinsupp d f n = f.component n :=
  rfl

/-- Recover an exact-support sequence using Mathlib's computed nonzero support. -/
noncomputable def scalarFiniteSchwartzDFinsuppToSequence
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzDFinsupp d) :
    ScalarFiniteSchwartzSequence d := by
  classical
  exact {
    support := f.support
    component := f
    mem_support_iff := fun _ => DFinsupp.mem_support_iff }

@[simp] theorem scalarFiniteSchwartzDFinsuppToSequence_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzDFinsupp d) (n : ℕ) :
    (scalarFiniteSchwartzDFinsuppToSequence d f).component n = f n :=
  rfl

/-- Exact-support finite sequences are equivalent to dependent finitely supported functions. -/
noncomputable def scalarFiniteSchwartzSequenceDFinsuppEquiv
    (d : EuclideanDimension) :
    ScalarFiniteSchwartzSequence d ≃ ScalarFiniteSchwartzDFinsupp d where
  toFun := scalarFiniteSchwartzSequenceToDFinsupp d
  invFun := scalarFiniteSchwartzDFinsuppToSequence d
  left_inv f := by
    apply ScalarFiniteSchwartzSequence.ext
    intro n
    rfl
  right_inv f := by
    apply DFinsupp.ext
    intro n
    rfl

/-- Named pointwise addition on exact-support finite sequences. -/
noncomputable def addScalarFiniteSchwartzSequence
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d :=
  (scalarFiniteSchwartzSequenceDFinsuppEquiv d).symm
    (scalarFiniteSchwartzSequenceDFinsuppEquiv d f +
      scalarFiniteSchwartzSequenceDFinsuppEquiv d g)

/-- Named pointwise negation on exact-support finite sequences. -/
noncomputable def negScalarFiniteSchwartzSequence
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d :=
  (scalarFiniteSchwartzSequenceDFinsuppEquiv d).symm
    (-scalarFiniteSchwartzSequenceDFinsuppEquiv d f)

/-- Named pointwise complex scalar multiplication on exact-support finite sequences. -/
noncomputable def smulScalarFiniteSchwartzSequence
    (d : EuclideanDimension) (c : ℂ) (f : ScalarFiniteSchwartzSequence d) :
    ScalarFiniteSchwartzSequence d :=
  (scalarFiniteSchwartzSequenceDFinsuppEquiv d).symm
    (c • scalarFiniteSchwartzSequenceDFinsuppEquiv d f)

@[simp] theorem addScalarFiniteSchwartzSequence_component
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (addScalarFiniteSchwartzSequence d f g).component n =
      f.component n + g.component n :=
  rfl

@[simp] theorem negScalarFiniteSchwartzSequence_component
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (negScalarFiniteSchwartzSequence d f).component n = -f.component n :=
  rfl

@[simp] theorem smulScalarFiniteSchwartzSequence_component
    (d : EuclideanDimension) (c : ℂ) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (smulScalarFiniteSchwartzSequence d c f).component n = c • f.component n :=
  rfl

/-- Addition support can shrink by cancellation but cannot escape the union of input supports. -/
theorem addScalarFiniteSchwartzSequence_support_subset
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) :
    (addScalarFiniteSchwartzSequence d f g).support ⊆ f.support ∪ g.support := by
  intro n hn
  have hnz := ((addScalarFiniteSchwartzSequence d f g).mem_support_iff n).mp hn
  rw [addScalarFiniteSchwartzSequence_component] at hnz
  contrapose! hnz
  have hnot : n ∉ f.support ∧ n ∉ g.support := by
    simpa [Finset.mem_union] using hnz
  have hf : f.component n = 0 := f.component_eq_zero_of_not_mem n hnot.1
  have hg : g.component n = 0 := g.component_eq_zero_of_not_mem n hnot.2
  rw [hf, hg]
  simp

/-- A nonzero complex scalar preserves exact sequence support. -/
@[simp] theorem smulScalarFiniteSchwartzSequence_support
    (d : EuclideanDimension) (c : ℂ) (hc : c ≠ 0)
    (f : ScalarFiniteSchwartzSequence d) :
    (smulScalarFiniteSchwartzSequence d c f).support = f.support := by
  ext n
  rw [(smulScalarFiniteSchwartzSequence d c f).mem_support_iff,
    f.mem_support_iff, smulScalarFiniteSchwartzSequence_component]
  simp [hc]

/-- The named additive commutative group transported from dependent finite support.
Install only locally with `letI`. -/
@[reducible] noncomputable def scalarFiniteSchwartzSequenceAddCommGroup
    (d : EuclideanDimension) : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
  Equiv.addCommGroup (scalarFiniteSchwartzSequenceDFinsuppEquiv d)

/-- The named complex module transported from dependent finite support.
Install the named additive group first, then this module, both with `letI`. -/
@[reducible] noncomputable def scalarFiniteSchwartzSequenceModule
    (d : EuclideanDimension) :
    @Module ℂ (ScalarFiniteSchwartzSequence d) Complex.instSemiring
      (scalarFiniteSchwartzSequenceAddCommGroup d).toAddCommMonoid :=
  Equiv.module ℂ (scalarFiniteSchwartzSequenceDFinsuppEquiv d)

/-- The transported instance addition is definitionally the named exact-support operation. -/
theorem scalarFiniteSchwartzSequence_instance_add_eq
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) :
    @Add.add _ (scalarFiniteSchwartzSequenceAddCommGroup d).toAdd f g =
      addScalarFiniteSchwartzSequence d f g :=
  rfl

/-- The transported instance scalar action is definitionally the named exact-support operation. -/
theorem scalarFiniteSchwartzSequence_instance_smul_eq
    (d : EuclideanDimension) (c : ℂ) (f : ScalarFiniteSchwartzSequence d) :
    @SMul.smul ℂ _ (scalarFiniteSchwartzSequenceModule d).toSMul c f =
      smulScalarFiniteSchwartzSequence d c f :=
  rfl

end YangMills
