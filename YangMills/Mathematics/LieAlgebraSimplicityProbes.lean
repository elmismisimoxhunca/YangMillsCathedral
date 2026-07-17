/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.LieAlgebraSimplicity

/-!
# Hostile probes for Lie-algebra simplicity

These probes enforce the two independent parts of Mathlib's simplicity interface: non-abelianness
and absence of proper nonzero Lie ideals. They are reusable mathematical checks, not gauge-group
or Yang–Mills witnesses.
-/

namespace YangMills.Mathematics.Probes

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- An abelian Lie algebra cannot be supplied as simple. -/
theorem abelian_simpleLieAlgebra_blocked [IsLieAbelian L]
    (simple : LieAlgebra.IsSimple R L) : False :=
  simple.non_abelian inferInstance

/-- A subsingleton Lie algebra cannot be supplied as simple. -/
theorem subsingleton_simpleLieAlgebra_blocked [Subsingleton L]
    (simple : LieAlgebra.IsSimple R L) : False :=
  LieAlgebra.not_isSimple_of_subsingleton R L simple

/-- A proper nonzero ideal cannot occur in a simple Lie algebra. -/
theorem proper_nonzero_ideal_blocked
    (simple : LieAlgebra.IsSimple R L) (ideal : LieIdeal R L)
    (nonzero : ideal ≠ ⊥) (proper : ideal ≠ ⊤) : False := by
  exact (simple.eq_bot_or_eq_top ideal).elim nonzero proper

end YangMills.Mathematics.Probes
