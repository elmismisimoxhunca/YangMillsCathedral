/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualAlgebraicPlancherel

/-!
# Hostile probes for algebraic Plancherel over the coordinate unitary dual
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualAlgebraicPlancherel
namespace Probes

open MeasureTheory

noncomputable section

universe uG

/-- The coefficient-side finite-support pairing is exactly normalized Haar pairing after
synthesis. -/
theorem exact_algebraic_coefficient_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : UnitaryMatrixDualCoefficientSpace G) :
    (∫ g, star (unitaryMatrixDualCoefficientSynthesis G A g) *
        unitaryMatrixDualCoefficientSynthesis G B g
      ∂normalizedCompactHaarMeasure G) =
      unitaryMatrixDualAlgebraicCoefficientPairing A B :=
  unitaryMatrixDualAlgebraicCoefficientSynthesis_pairing A B

/-- The all-coordinate-class Fourier-side algebraic Plancherel formula retains every exact
representation-dimension weight. -/
theorem exact_algebraic_fourier_plancherel
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : UnitaryMatrixDualCoefficientSpace G) :
    (∫ g, star (unitaryMatrixDualCoefficientSynthesis G A g) *
        unitaryMatrixDualCoefficientSynthesis G B g
      ∂normalizedCompactHaarMeasure G) =
      unitaryMatrixDualAlgebraicFourierPairing A B :=
  unitaryMatrixDualAlgebraicCoefficientSynthesis_fourier_plancherel A B

/-- Coefficient and Fourier pairings agree exactly on the dependent finite-support carrier. -/
theorem exact_coefficient_fourier_pairing_agreement
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : UnitaryMatrixDualCoefficientSpace G) :
    unitaryMatrixDualAlgebraicCoefficientPairing A B =
      unitaryMatrixDualAlgebraicFourierPairing A B :=
  unitaryMatrixDualAlgebraicCoefficientPairing_eq_fourierPairing A B

/-- Hostile exactness probe: changing the dimension-weighted all-class Fourier pairing is
contradictory. -/
theorem changed_algebraic_plancherel_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (A B : UnitaryMatrixDualCoefficientSpace G)
    (changed :
      (∫ g, star (unitaryMatrixDualCoefficientSynthesis G A g) *
          unitaryMatrixDualCoefficientSynthesis G B g
        ∂normalizedCompactHaarMeasure G) ≠
        unitaryMatrixDualAlgebraicFourierPairing A B) : False :=
  changed
    (unitaryMatrixDualAlgebraicCoefficientSynthesis_fourier_plancherel A B)

/-- Scope probe: the theorem quantifies over the direct-sum carrier itself, whose elements have
finite support; it does not produce a summation or inversion theorem for an arbitrary family over
the dual. -/
theorem finite_support_carrier_retained
    {G : Type uG} [Group G] [TopologicalSpace G]
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ support : Finset (UnitaryMatrixDual G),
      ∀ q, q ∉ support → unitaryMatrixDualCoefficientAt q A = 0 := by
  classical
  refine ⟨A.support, ?_⟩
  intro q outside
  change A q = 0
  exact DFinsupp.notMem_support_iff.mp outside

end

end Probes
end UnitaryMatrixDualAlgebraicPlancherel
end Mathematics
end YangMills
