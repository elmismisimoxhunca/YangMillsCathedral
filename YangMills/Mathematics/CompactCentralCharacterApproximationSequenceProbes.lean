/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactCentralCharacterApproximationSequence

/-!
# Hostile probes for finite character-approximation sequences
-/

namespace YangMills
namespace Mathematics
namespace CompactCentralCharacterApproximationSequence
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Every selected approximation stage has the exact strict `1/(n+1)` uniform bound. -/
theorem exact_stage_error_bound
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (n : ℕ) :
    ‖(unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)) -
      (f : C(G, ℂ))‖ < (1 / (n + 1 : ℝ)) :=
  centralCharacterApproximationCoefficients_norm_sub_lt density f n

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Every stage is genuinely finitely supported; no countability theorem for the whole dual is
hidden in the sequence. -/
theorem exact_stage_finite_support
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (n : ℕ) :
    Function.HasFiniteSupport
      (centralCharacterApproximationCoefficients density f n) :=
  Finsupp.hasFiniteSupport _

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Hostile bound probe: denying the prescribed bound at one stage is contradictory. -/
theorem changed_stage_error_bound_blocked
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (n : ℕ)
    (changed : (1 / (n + 1 : ℝ)) ≤
      ‖(unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)) -
        (f : C(G, ℂ))‖) : False :=
  (not_lt_of_ge changed)
    (centralCharacterApproximationCoefficients_norm_sub_lt density f n)

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The selected finite character sequence converges uniformly in `C(G, ℂ)`. -/
theorem exact_uniform_sequence_convergence
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n =>
      (unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)))
      Filter.atTop (nhds (f : C(G, ℂ))) :=
  tendsto_centralCharacterApproximationCoefficients density f

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The same finite character sequence converges in the exact continuous-central subtype. -/
theorem exact_central_subtype_sequence_convergence
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n => unitaryMatrixDualCentralCharacterSynthesis G
      (centralCharacterApproximationCoefficients density f n))
      Filter.atTop (nhds f) :=
  tendsto_centralCharacterApproximationCoefficients_in_central density f

omit [T2Space G] in
/-- The same finite character sequence converges in normalized-Haar `L²`. -/
theorem exact_L2_sequence_convergence
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G
      (centralCharacterApproximationCoefficients density f n))
      Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  tendsto_centralCharacterApproximationCoefficients_L2 density f

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Hostile limit probe: any alternative uniform limit of the same selected sequence equals the
expected central function. -/
theorem alternative_uniform_limit_eq
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) (alternative : C(G, ℂ))
    (alternativeLimit : Filter.Tendsto (fun n =>
      (unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)))
      Filter.atTop (nhds alternative)) :
    alternative = (f : C(G, ℂ)) :=
  tendsto_nhds_unique alternativeLimit
    (tendsto_centralCharacterApproximationCoefficients density f)

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Hostile convergence probe: the proved uniform convergence cannot fail. -/
theorem changed_uniform_limit_blocked
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G)
    (failed : ¬ Filter.Tendsto (fun n =>
      (unitaryMatrixDualCentralCharacterSynthesis G
        (centralCharacterApproximationCoefficients density f n) : C(G, ℂ)))
      Filter.atTop (nhds (f : C(G, ℂ)))) : False :=
  failed (tendsto_centralCharacterApproximationCoefficients density f)

variable [SecondCountableTopology G]

/-- Faithful finite matrix coordinates produce a uniformly convergent finite-character sequence. -/
theorem exact_faithful_sequence_existence
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
        Filter.atTop (nhds (f : C(G, ℂ))) :=
  exists_tendsto_finiteCharacterSynthesis_of_faithful faithful f

/-- Faithful finite matrix coordinates produce the corresponding normalized-Haar `L²` convergence. -/
theorem exact_faithful_L2_sequence_existence
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
        Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  exists_tendsto_finiteCharacterSynthesis_L2_of_faithful faithful f

/-- One same finite-support sequence witnesses both faithful uniform and `L²` convergence. -/
theorem exact_faithful_same_sequence_existence
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (f : continuousCentralFunctionStarSubalgebra G) :
    ∃ coefficients : ℕ → UnitaryMatrixDualCharacterCoefficients G,
      Filter.Tendsto (fun n =>
        (unitaryMatrixDualCentralCharacterSynthesis G (coefficients n) : C(G, ℂ)))
          Filter.atTop (nhds (f : C(G, ℂ))) ∧
      Filter.Tendsto (fun n => unitaryMatrixDualL2CharacterSynthesis G (coefficients n))
        Filter.atTop (nhds (normalizedCompactHaarCentralContinuousToL2 G f)) :=
  exists_tendsto_finiteCharacterSynthesis_and_L2_of_faithful faithful f

end

end Probes
end CompactCentralCharacterApproximationSequence
end Mathematics
end YangMills
