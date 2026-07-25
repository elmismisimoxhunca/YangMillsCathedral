/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Source-facing view of simple Lie algebras

Hall's pinned notes, printed p. 115, describe a simple Lie algebra as having dimension at least two
and no ideals other than zero and the whole algebra. Mathlib's `LieAlgebra.IsSimple` uses the
ideal condition together with explicit non-abelianness. This module records that exact interface and
its anti-vacuity consequences; it introduces no competing definition.

This is reusable mathematics. It does not assert that a Lie group is compact, connected, or an
admissible Yang–Mills gauge group.
-/

namespace YangMills.Mathematics

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- Mathlib simplicity is exactly the conjunction used by this project: every Lie ideal is bottom
or top, and the algebra is not abelian. -/
theorem lieAlgebra_isSimple_iff_ideals_and_nonabelian :
    LieAlgebra.IsSimple R L ↔
      (∀ ideal : LieIdeal R L, ideal = ⊥ ∨ ideal = ⊤) ∧ ¬IsLieAbelian L := by
  constructor
  · intro simple
    exact ⟨simple.eq_bot_or_eq_top, simple.non_abelian⟩
  · rintro ⟨ideals, nonabelian⟩
    exact ⟨ideals, nonabelian⟩

/-- A simple Lie algebra is non-abelian by definition in the selected Mathlib interface. -/
theorem isSimple_not_isLieAbelian (simple : LieAlgebra.IsSimple R L) :
    ¬IsLieAbelian L :=
  simple.non_abelian

/-- Every ideal in a simple Lie algebra is bottom or top. -/
theorem isSimple_ideal_eq_bot_or_eq_top
    (simple : LieAlgebra.IsSimple R L) (ideal : LieIdeal R L) :
    ideal = ⊥ ∨ ideal = ⊤ :=
  simple.eq_bot_or_eq_top ideal

/-- A simple Lie algebra cannot have a subsingleton carrier. -/
theorem isSimple_to_nontrivial (simple : LieAlgebra.IsSimple R L) : Nontrivial L := by
  rw [← not_subsingleton_iff_nontrivial]
  intro subsingleton
  letI : Subsingleton L := subsingleton
  exact LieAlgebra.not_isSimple_of_subsingleton R L simple

end YangMills.Mathematics
