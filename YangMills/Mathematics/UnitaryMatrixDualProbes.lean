/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDual

/-!
# Hostile probes for the coordinate unitary dual
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDual
namespace Probes

noncomputable section

universe uG uι

/-- Quotient equality is exactly representation equivalence, not equality of stored coordinates. -/
theorem class_equality_iff_equivalence
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    unitaryMatrixDualClass ρ = unitaryMatrixDualClass σ ↔
      ρ.IsEquivalent σ :=
  unitaryMatrixDualClass_eq_iff ρ σ

/-- Equivalent representations cannot have different finite coordinate dimensions. -/
theorem equivalent_dimensions_agree
    {G : Type uG} [Group G] [TopologicalSpace G]
    {ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G}
    (equivalent : ρ.IsEquivalent σ) :
    ρ.dimension = σ.dimension :=
  ContinuousUnitaryIrreducibleMatrixRepresentation.dimension_eq_of_isEquivalent
    equivalent

/-- Every bundled coordinate representation is covered by the selected representative of one dual
class. -/
theorem every_bundled_representation_is_covered
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    ρ.IsEquivalent
      (unitaryMatrixDualRepresentative (unitaryMatrixDualClass ρ)) :=
  unitaryMatrixDual_equivalent_representative ρ

/-- Hostile quotient probe: an equivalence between selected representatives of distinct classes is
impossible. -/
theorem equivalent_distinct_dual_classes_blocked
    {G : Type uG} [Group G] [TopologicalSpace G]
    (q r : UnitaryMatrixDual G) (distinct : q ≠ r)
    (equivalence : Representation.Equiv
      (matrixRepresentation (unitaryMatrixDualRepresentation r))
      (matrixRepresentation (unitaryMatrixDualRepresentation q))) : False :=
  (unitaryMatrixDual_representative_inequivalent distinct).false equivalence

/-- An injectively labelled finite or infinite family of dual classes supplies the exact oriented
pairwise-inequivalence certificate used by coefficient-family Fourier analysis. -/
theorem injective_labels_are_pairwise_inequivalent
    {G : Type uG} [Group G] [TopologicalSpace G]
    {ι : Type uι} (label : ι → UnitaryMatrixDual G)
    (injectiveLabel : Function.Injective label)
    (i j : ι) (distinct : i ≠ j) :
    IsEmpty (Representation.Equiv
      (matrixRepresentation
        (unitaryMatrixDualRepresentation (label j)))
      (matrixRepresentation
        (unitaryMatrixDualRepresentation (label i)))) :=
  unitaryMatrixDual_pairwiseInequivalent
    label injectiveLabel i j distinct

/-- Hostile coverage boundary: the quotient construction covers exactly the bundled coordinate
representations; any broader abstract representation still requires a separate coordinate/unitary
realization theorem. -/
theorem coverage_retains_exact_bundle
    {G : Type uG} [Group G] [TopologicalSpace G]
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    Nonempty (Representation.Equiv
      (matrixRepresentation ρ.representation)
      (matrixRepresentation
        (unitaryMatrixDualRepresentation (unitaryMatrixDualClass ρ)))) :=
  unitaryMatrixDual_equivalent_representative ρ

end

end Probes
end UnitaryMatrixDual
end Mathematics
end YangMills
