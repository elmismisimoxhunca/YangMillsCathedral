/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactGroupCharacterCentralizationBridge

/-!
# Hostile probes for the character-centralization bridge
-/

namespace YangMills
namespace Mathematics
namespace CompactGroupCharacterCentralizationBridge
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]

/-- The centralization map is genuinely onto the exact continuous-central carrier. -/
theorem exact_centralization_surjective
    (data : CompactGroupCharacterCentralizationData G) :
    Function.Surjective data.centralization :=
  data.centralization_surjective

/-- The exact identity-on-central-functions law forces preservation of one. -/
theorem exact_centralization_one
    (data : CompactGroupCharacterCentralizationData G) :
    data.centralization (1 : C(G, ℂ)) =
      (1 : continuousCentralFunctionStarSubalgebra G) :=
  data.centralization_one

/-- Hostile noncollapse probe: a valid centralization map cannot be the zero map. -/
theorem zero_centralization_blocked
    (data : CompactGroupCharacterCentralizationData G)
    (collapsed : data.centralization = 0) : False := by
  have hone := data.centralization_one
  rw [collapsed] at hone
  exact one_ne_zero hone.symm

/-- Every selected-dual finite coefficient synthesis has an exact finite selected-character image. -/
theorem exact_coefficient_to_character_image
    (data : CompactGroupCharacterCentralizationData G)
    (A : UnitaryMatrixDualCoefficientSpace G) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      data.centralization (unitaryMatrixDualContinuousCoefficientSynthesis G A) =
        unitaryMatrixDualCentralCharacterSynthesis G c :=
  data.maps_coefficient_synthesis A

/-- Full continuous coefficient density plus centralization data implies central character density. -/
theorem exact_full_to_central_density_bridge
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  density.hasCentralContinuousPeterWeylDensity data

/-- Hostile bridge probe: if full density holds but central density fails, no valid centralization
data can exist. -/
theorem failed_central_density_blocks_centralization
    (density : UnitaryMatrixDual.HasContinuousPeterWeylDensity G)
    (failed : ¬ UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G) :
    ¬ Nonempty (CompactGroupCharacterCentralizationData G) := by
  rintro ⟨data⟩
  exact failed (density.hasCentralContinuousPeterWeylDensity data)

variable [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Faithful finite matrix coordinates plus the exact Hall centralization bridge imply uniform
central character density. -/
theorem exact_faithful_central_density
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G :=
  unitaryMatrixDual_hasCentralContinuousPeterWeylDensity_of_faithful_of_centralization faithful data

/-- The same explicit hypotheses imply the named central normalized-Haar `L²` target. -/
theorem exact_faithful_central_L2_completeness
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (data : CompactGroupCharacterCentralizationData G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful_of_centralization faithful data

/-- Hostile endpoint probe: failed central `L²` completeness blocks the conjunction of faithful
coordinates and valid centralization data. -/
theorem failed_central_L2_blocks_faithful_centralization
    (faithful : ContinuousFaithfulFiniteMatrixRepresentation G)
    (failed : ¬ UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G) :
    ¬ Nonempty (CompactGroupCharacterCentralizationData G) := by
  rintro ⟨data⟩
  exact failed
    (unitaryMatrixDual_hasCentralL2PeterWeylCompleteness_of_faithful_of_centralization faithful data)

end

end Probes
end CompactGroupCharacterCentralizationBridge
end Mathematics
end YangMills
