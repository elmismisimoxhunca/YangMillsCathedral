/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCentralContinuousFunctions

/-!
# Hostile probes for continuous central functions and character density
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCentralContinuousFunctions
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Central-function membership retains the exact common-conjugator equation. -/
theorem exact_central_membership (f : C(G, ℂ)) :
    f ∈ continuousCentralFunctionStarSubalgebra G ↔
      ∀ g h : G, f (h * g * h⁻¹) = f g :=
  mem_continuousCentralFunctionStarSubalgebra_iff f

/-- Hostile centrality probe: a changed conjugation value excludes membership. -/
theorem changed_conjugation_value_blocks_centrality
    (f : C(G, ℂ)) {g h : G} (changed : f (h * g * h⁻¹) ≠ f g) :
    f ∉ continuousCentralFunctionStarSubalgebra G := by
  intro hf
  exact changed ((mem_continuousCentralFunctionStarSubalgebra_iff f).mp hf g h)

/-- Every finite character synthesis carries exact centrality. -/
theorem exact_character_synthesis_centrality
    (c : UnitaryMatrixDualCharacterCoefficients G) (g h : G) :
    ((unitaryMatrixDualCentralCharacterSynthesis G c :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) (h * g * h⁻¹) =
    ((unitaryMatrixDualCentralCharacterSynthesis G c :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) g :=
  (unitaryMatrixDualCentralCharacterSynthesis G c).property g h

/-- The restricted synthesis retains the unchanged finite character sum. -/
theorem exact_restricted_character_synthesis
    (c : UnitaryMatrixDualCharacterCoefficients G) (g : G) :
    ((unitaryMatrixDualCentralCharacterSynthesis G c :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) g =
      unitaryMatrixDualCharacterSynthesis G c g :=
  unitaryMatrixDualCentralCharacterSynthesis_apply c g

/-- The named compact-group target is definitionally dense range in the exact central carrier. -/
theorem exact_central_density_target [CompactSpace G] :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G ↔
      DenseRange (unitaryMatrixDualCentralCharacterSynthesis G) :=
  Iff.rfl

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Restricting the codomain to central functions does not collapse finite character coefficients. -/
theorem exact_restricted_character_synthesis_injective :
    Function.Injective (unitaryMatrixDualCentralCharacterSynthesis G) :=
  unitaryMatrixDualCentralCharacterSynthesis_injective

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Any future inhabitant of the target gives finite character approximation at every positive
uniform tolerance. -/
theorem exact_character_approximation_from_target
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖(unitaryMatrixDualCentralCharacterSynthesis G c : C(G, ℂ)) - (f : C(G, ℂ))‖ < ε :=
  density.exists_character_approximation f hε

omit [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- Hostile approximation probe: a central function with no finite character approximant blocks the
density target. -/
theorem missing_character_approximation_blocks_target
    (f : continuousCentralFunctionStarSubalgebra G) {ε : ℝ} (hε : 0 < ε)
    (missing : ∀ c : UnitaryMatrixDualCharacterCoefficients G,
      ε ≤ ‖(unitaryMatrixDualCentralCharacterSynthesis G c : C(G, ℂ)) -
        (f : C(G, ℂ))‖) :
    ¬ UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G := by
  intro density
  rcases density.exists_character_approximation f hε with ⟨c, hc⟩
  exact (not_lt_of_ge (missing c)) hc

end

end Probes
end UnitaryMatrixDualCentralContinuousFunctions
end Mathematics
end YangMills
