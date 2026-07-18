/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerFiniteSequenceModule
import YangMills.Euclidean.SchwingerFiniteSequenceProbes

/-!
# Hostile probes for the named finite-sequence complex module

The probes expose both directions of the dependent-finite-support equivalence, exact pointwise
operations, cancellation-induced support shrinkage, preservation under nonzero scalars, and local
rather than global instance installation.
-/

namespace YangMills.Euclidean.SchwingerFiniteSequenceModule.Probes

/-- Passing an exact sequence through dependent finite support and back changes nothing. -/
theorem sequence_dfinsupp_round_trip
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    scalarFiniteSchwartzDFinsuppToSequence d
      (scalarFiniteSchwartzSequenceToDFinsupp d f) = f :=
  (scalarFiniteSchwartzSequenceDFinsuppEquiv d).left_inv f

/-- Passing dependent finite support through the exact sequence carrier and back changes nothing. -/
theorem dfinsupp_sequence_round_trip
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzDFinsupp d) :
    scalarFiniteSchwartzSequenceToDFinsupp d
      (scalarFiniteSchwartzDFinsuppToSequence d f) = f :=
  (scalarFiniteSchwartzSequenceDFinsuppEquiv d).right_inv f

/-- Named addition acts on the exact same dependent component. -/
theorem exact_add_component
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (addScalarFiniteSchwartzSequence d f g).component n =
      f.component n + g.component n :=
  addScalarFiniteSchwartzSequence_component d f g n

/-- Named scalar multiplication acts on the exact same dependent component. -/
theorem exact_smul_component
    (d : EuclideanDimension) (c : ℂ) (f : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    (smulScalarFiniteSchwartzSequence d c f).component n = c • f.component n :=
  smulScalarFiniteSchwartzSequence_component d c f n

/-- Adding a sequence to its pointwise negative gives the existing unrestricted zero sequence. -/
theorem add_neg_is_exact_zero
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    addScalarFiniteSchwartzSequence d f
      (negScalarFiniteSchwartzSequence d f) = zeroScalarFiniteSchwartzSequence d := by
  apply ScalarFiniteSchwartzSequence.ext
  intro n
  simp
  rfl

/-- Exact support shrinks to empty under complete cancellation; it is not retained as an arbitrary
union bound. -/
theorem cancellation_removes_support
    (d : EuclideanDimension) (f : ScalarFiniteSchwartzSequence d) :
    (addScalarFiniteSchwartzSequence d f
      (negScalarFiniteSchwartzSequence d f)).support = ∅ := by
  rw [add_neg_is_exact_zero]
  rfl

/-- Multiplication by `i` preserves the explicit singleton bump's exact support. -/
theorem imaginary_scalar_preserves_bump_support
    (d : EuclideanDimension) :
    (smulScalarFiniteSchwartzSequence d Complex.I
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support =
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence.support := by
  apply smulScalarFiniteSchwartzSequence_support
  exact Complex.I_ne_zero

/-- The nonzero arity-one bump cannot disappear after multiplication by `i`. -/
theorem imaginary_scaled_bump_one_mem_support
    (d : EuclideanDimension) :
    1 ∈ (smulScalarFiniteSchwartzSequence d Complex.I
      (singletonPositiveTimeBumpSequence d).toFiniteSchwartzSequence).support := by
  rw [imaginary_scalar_preserves_bump_support]
  rw [_root_.YangMills.Euclidean.SchwingerFiniteSequence.Probes.forgotten_singleton_bump_support]
  simp

/-- The named instances are installed locally and expose exact pointwise module operations. -/
theorem locally_installed_module_component
    (d : EuclideanDimension) (c : ℂ)
    (f g : ScalarFiniteSchwartzSequence d) (n : ℕ) :
    letI : AddCommGroup (ScalarFiniteSchwartzSequence d) :=
      scalarFiniteSchwartzSequenceAddCommGroup d
    letI : Module ℂ (ScalarFiniteSchwartzSequence d) :=
      scalarFiniteSchwartzSequenceModule d
    (c • (f + g)).component n = c • (f.component n + g.component n) := by
  rfl

/-- Addition support may shrink, but can never introduce an arity outside both inputs. -/
theorem addition_support_cannot_escape_union
    (d : EuclideanDimension) (f g : ScalarFiniteSchwartzSequence d)
    (n : ℕ) (hmem : n ∈ (addScalarFiniteSchwartzSequence d f g).support) :
    n ∈ f.support ∪ g.support :=
  addScalarFiniteSchwartzSequence_support_subset d f g hmem

end YangMills.Euclidean.SchwingerFiniteSequenceModule.Probes
