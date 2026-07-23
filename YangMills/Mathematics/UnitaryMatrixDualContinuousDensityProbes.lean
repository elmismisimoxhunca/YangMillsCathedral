/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualContinuousDensity

/-!
# Hostile probes for the selected-dual continuous density target
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualContinuousDensity
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Continuous coefficient synthesis retains the exact finite matrix sum pointwise. -/
theorem exact_continuous_synthesis_evaluation
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (A : Matrix (Fin n) (Fin n) ℂ) (g : G) :
    continuousMatrixCoefficientSynthesis ρ hρ A g =
      ∑ i, ∑ j, A i j * ρ g i j :=
  rfl

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Selected quotient representatives span exactly the earlier all-presentation coefficient span. -/
theorem exact_selected_range_eq_span :
    LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) =
      compactUnitaryCoefficientSpan (G := G) :=
  unitaryMatrixDualContinuousCoefficientSynthesis_range_eq_span

/-- Hostile range probe: changing the exact selected-range identification is contradictory. -/
theorem changed_selected_range_blocked
    (changed : LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) ≠
      compactUnitaryCoefficientSpan (G := G)) : False :=
  changed unitaryMatrixDualContinuousCoefficientSynthesis_range_eq_span

omit [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The named continuous Peter–Weyl target is definitionally selected-range density. -/
theorem exact_continuous_density_target :
    UnitaryMatrixDual.HasContinuousPeterWeylDensity G ↔
      Dense (LinearMap.range (unitaryMatrixDualContinuousCoefficientSynthesis G) : Set C(G, ℂ)) :=
  Iff.rfl

/-- The target is equivalently density of the exact finite coefficient span. -/
theorem exact_continuous_density_iff_span_dense :
    UnitaryMatrixDual.HasContinuousPeterWeylDensity G ↔
      Dense (compactUnitaryCoefficientSpan (G := G) : Set C(G, ℂ)) :=
  unitaryMatrixDual_hasContinuousPeterWeylDensity_iff_span_dense

/-- A faithful finite matrix representation supplies the target, retaining the conditional scope. -/
theorem exact_faithful_continuous_density
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G) :
    UnitaryMatrixDual.HasContinuousPeterWeylDensity G :=
  unitaryMatrixDual_hasContinuousPeterWeylDensity_of_faithful faithful

/-- Any future proof of the general continuous target automatically supplies the existing `L²`
completeness target through normalized-Haar regularity. -/
theorem exact_continuous_to_L2_bridge
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasL2PeterWeylCompleteness G :=
  density.hasL2PeterWeylCompleteness

/-- Hostile bridge probe: continuous density cannot coexist with failed `L²` completeness. -/
theorem continuous_density_with_failed_L2_blocked
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (failed : ¬ UnitaryMatrixDual.HasL2PeterWeylCompleteness G) : False :=
  failed density.hasL2PeterWeylCompleteness

end

end Probes
end UnitaryMatrixDualContinuousDensity
end Mathematics
end YangMills
