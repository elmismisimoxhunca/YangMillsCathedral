/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactCentralCharacterCoefficientConvergence

/-!
# Hostile probes for coefficientwise central-character convergence
-/

namespace YangMills
namespace Mathematics
namespace CompactCentralCharacterCoefficientConvergence
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Every selected coordinate converges to the exact `L²` character analysis. -/
theorem exact_coordinate_analysis_limit
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    Filter.Tendsto (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds (unitaryMatrixDualL2CharacterAnalysis q
        (normalizedCompactHaarCentralContinuousToL2 G f))) :=
  tendsto_centralCharacterApproximationCoefficients_apply density f q

/-- The same limit is the exact normalized-Haar integral with conjugated character in the first
slot. -/
theorem exact_coordinate_integral_limit
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G) :
    Filter.Tendsto (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds (∫ g, star (unitaryMatrixDualCharacter q g) *
        (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G)) :=
  tendsto_centralCharacterApproximationCoefficients_apply_integral density f q

/-- Hostile uniqueness probe: any alternative coordinate limit equals the exact character
coefficient. -/
theorem alternative_coordinate_limit_eq
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G)
    (alternative : ℂ)
    (alternativeLimit : Filter.Tendsto
      (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds alternative)) :
    alternative = ∫ g, star (unitaryMatrixDualCharacter q g) *
      (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G :=
  tendsto_nhds_unique alternativeLimit
    (tendsto_centralCharacterApproximationCoefficients_apply_integral density f q)

/-- Hostile convergence probe: failure of the exact integral-coordinate limit is contradictory. -/
theorem changed_coordinate_limit_blocked
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (q : UnitaryMatrixDual G)
    (failed : ¬ Filter.Tendsto
      (fun n => centralCharacterApproximationCoefficients density f n q)
      Filter.atTop (nhds (∫ g, star (unitaryMatrixDualCharacter q g) *
        (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G))) : False :=
  failed (tendsto_centralCharacterApproximationCoefficients_apply_integral density f q)

variable [SecondCountableTopology G]

/-- Faithful finite coordinates produce one same sequence with uniform, `L²`, and all-coordinate
convergence. -/
theorem exact_faithful_same_sequence_all_limits
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
          Filter.atTop (nhds (f : C(G, ℂ))) ∧
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
          Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) ∧
      ∀ q : UnitaryMatrixDual G,
        Filter.Tendsto (fun n => coefficients n q) Filter.atTop
          (nhds (∫ g, star (unitaryMatrixDualCharacter q g) *
            (f : C(G, ℂ)) g ∂normalizedCompactHaarMeasure G)) :=
  exists_tendsto_finiteCharacterSynthesis_and_L2_and_coefficients_of_faithful faithful f

end

end Probes
end CompactCentralCharacterCoefficientConvergence
end Mathematics
end YangMills
