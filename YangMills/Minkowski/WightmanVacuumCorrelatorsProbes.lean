/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanVacuumCorrelators

/-!
# Hostile probes for algebraic smeared Wightman correlators

These probes lock normalization, operator order, the exact selected vacuum, the exact coherent
one-point distribution, and an explicit nonzero test. They do not assert joint temperedness,
analyticity, Euclidean continuation, or a nonzero correlator value.
-/

namespace YangMills.Minkowski.WightmanVacuumCorrelators.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D)

/-- The empty correlator is exactly one and hence cannot be zero. -/
theorem empty_correlator_exact :
    scalarWightmanVacuumExpectation fieldData [] = 1 :=
  scalarWightmanVacuumExpectation_nil fieldData

/-- Empty-correlator normalization blocks the identically-zero family. -/
theorem empty_correlator_ne_zero :
    scalarWightmanVacuumExpectation fieldData [] ≠ 0 := by
  rw [scalarWightmanVacuumExpectation_nil]
  norm_num

/-- The one-point value uses the exact field and exact selected domain vacuum. -/
theorem singleton_correlator_exact
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f] =
      inner ℂ vacuumData.vacuum
        ((fieldData.field f D.vacuumInDomain : D.domain) : H) :=
  scalarWightmanVacuumExpectation_singleton fieldData f

/-- The same one-point value is evaluated by the exact coherent tempered matrix element. -/
theorem singleton_matrixElement_exact
    (f : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f] =
      fieldData.matrixElement D.vacuumInDomain D.vacuumInDomain f :=
  scalarWightmanVacuumExpectation_singleton_eq_matrixElement fieldData f

/-- The two-point value has exact order `Φ(f) Φ(g) Ω`. -/
theorem pair_correlator_order_exact
    (f g : ScalarMinkowskiSchwartzTestFunction d) :
    scalarWightmanVacuumExpectation fieldData [f, g] =
      inner ℂ vacuumData.vacuum
        ((fieldData.field f (fieldData.field g D.vacuumInDomain) : D.domain) : H) :=
  scalarWightmanVacuumExpectation_pair fieldData f g

/-- A swapped replacement is rejected whenever the two ordered vacuum matrix elements differ. -/
theorem swapped_pair_replacement_blocked
    (f g : ScalarMinkowskiSchwartzTestFunction d)
    (hmismatch : inner ℂ vacuumData.vacuum
      ((fieldData.field g (fieldData.field f D.vacuumInDomain) : D.domain) : H) ≠
      inner ℂ vacuumData.vacuum
      ((fieldData.field f (fieldData.field g D.vacuumInDomain) : D.domain) : H)) :
    scalarWightmanVacuumExpectation fieldData [f, g] ≠
      inner ℂ vacuumData.vacuum
        ((fieldData.field g (fieldData.field f D.vacuumInDomain) : D.domain) : H) := by
  rw [scalarWightmanVacuumExpectation_pair]
  exact fun h => hmismatch h.symm

/-- The explicit nonzero bump enters the exact singleton correlator; no nonzero expectation is
fabricated. -/
theorem explicit_bump_singleton_exact :
    scalarWightmanVacuumExpectation fieldData [scalarMinkowskiSchwartzBump d] =
      fieldData.matrixElement D.vacuumInDomain D.vacuumInDomain
        (scalarMinkowskiSchwartzBump d) :=
  scalarWightmanVacuumExpectation_singleton_eq_matrixElement fieldData
    (scalarMinkowskiSchwartzBump d)

end YangMills.Minkowski.WightmanVacuumCorrelators.Probes
