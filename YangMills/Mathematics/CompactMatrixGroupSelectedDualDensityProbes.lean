/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactMatrixGroupSelectedDualDensity

/-!
# Hostile probes for selected-dual compact matrix-group density
-/

namespace YangMills
namespace Mathematics
namespace CompactMatrixGroupSelectedDualDensity
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
/-- The explicit trivial representation is literally the one matrix at every group element. -/
theorem exact_trivial_representation (g : G) :
    trivialOneDimensionalMatrixRepresentation G g = 1 :=
  rfl

/-- The trivial bundle retains positive dimension, continuity, unitarity, and irreducibility
on the same representative. -/
theorem exact_trivial_bundle_properties :
    (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).dimension = 1 ∧
    Continuous (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).representation ∧
    (∀ g, star ((trivialContinuousUnitaryIrreducibleMatrixRepresentation G).representation g) *
      (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).representation g = 1) ∧
    Representation.IsIrreducible (matrixRepresentation
      (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).representation) :=
  ⟨rfl,
    (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).continuous_representation,
    (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).unitary_representation,
    (trivialContinuousUnitaryIrreducibleMatrixRepresentation G).irreducible_representation⟩

/-- Every bundle is exactly equivalent to the representative selected for its own quotient class. -/
theorem exact_selected_representative_equivalence
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G) :
    Nonempty (Representation.Equiv (matrixRepresentation ρ.representation)
      (matrixRepresentation (unitaryMatrixDualRepresentation (unitaryMatrixDualClass ρ)))) :=
  ⟨unitaryMatrixDualSelectedRepresentativeEquiv ρ⟩

/-- The selected coefficient matrix synthesizes the unchanged original coefficient. -/
theorem exact_selected_coefficient_synthesis
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension) :
    unitaryMatrixDualCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle (unitaryMatrixDualClass ρ)
        (unitaryMatrixDualSelectedCoefficientMatrix ρ row column)) =
      fun g => ρ.representation g row column :=
  unitaryMatrixDualCoefficientSynthesis_selectedCoefficient ρ row column

/-- Hostile presentation probe: changing the selected synthesis is contradictory. -/
theorem changed_selected_coefficient_synthesis_blocked
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (row column : Fin ρ.dimension)
    (changed : unitaryMatrixDualCoefficientSynthesis G
      (unitaryMatrixDualCoefficientSingle (unitaryMatrixDualClass ρ)
        (unitaryMatrixDualSelectedCoefficientMatrix ρ row column)) ≠
      fun g => ρ.representation g row column) : False :=
  changed (unitaryMatrixDualCoefficientSynthesis_selectedCoefficient ρ row column)

/-- The explicit trivial class prevents constant-one membership from being vacuous. -/
theorem exact_one_in_selected_continuous_range :
    (1 : C(G, ℂ)) ∈ LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) :=
  one_mem_unitaryMatrixDualContinuousRange

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Under the source-visible faithful hypothesis, the selected quotient-dual synthesis—not merely
the all-presentation star algebra—has dense continuous range. -/
theorem exact_selected_continuous_density
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    Dense (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) :=
  unitaryMatrixDualContinuousCoefficientSynthesis_denseRange_of_faithful faithful

/-- Hostile density probe: changing selected-dual continuous density is contradictory. -/
theorem changed_selected_continuous_density_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (changed : ¬ Dense
      (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ))) : False :=
  changed (unitaryMatrixDualContinuousCoefficientSynthesis_denseRange_of_faithful faithful)

omit [T2Space G] in
/-- The canonical continuous-to-`L²` map sends the selected continuous synthesis range into the
selected algebraic `L²` range. -/
theorem exact_continuous_to_L2_range_inclusion :
    normalizedCompactHaarContinuousToL2 G ''
      (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) ⊆
      (unitaryMatrixDualL2AlgebraicRange G : Set (NormalizedCompactHaarL2 G)) :=
  unitaryMatrixDual_toLp_continuousRange_subset_L2AlgebraicRange

/-- Normalized-Haar regularity and finiteness transfer conditional continuous density to the existing
coordinate-dual Peter–Weyl completeness target. -/
theorem exact_conditional_L2_completeness
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasL2PeterWeylCompleteness G :=
  unitaryMatrixDual_hasL2PeterWeylCompleteness_of_faithful faithful

/-- Hostile `L²` probe: negating the conditional completeness theorem is contradictory. -/
theorem changed_conditional_L2_completeness_blocked
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (changed : ¬ UnitaryMatrixDual.HasL2PeterWeylCompleteness G) : False :=
  changed (unitaryMatrixDual_hasL2PeterWeylCompleteness_of_faithful faithful)

end

end Probes
end CompactMatrixGroupSelectedDualDensity
end Mathematics
end YangMills
