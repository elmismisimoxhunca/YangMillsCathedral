/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCentralL2Span

/-!
# Hostile probes for the central normalized-Haar L² span
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCentralL2Span
namespace Probes

noncomputable section

open MeasureTheory

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- The central `L²` target is exactly equality of the two named closed spans. -/
theorem exact_central_L2_target :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G ↔
      unitaryMatrixDualL2CharacterClosedSpan G =
        normalizedCompactHaarContinuousCentralL2ClosedSpan G :=
  Iff.rfl

omit [T2Space G] in
/-- Finite character synthesis is always in the continuous-central `L²` range. -/
theorem exact_character_range_inclusion :
    unitaryMatrixDualL2CharacterAlgebraicRange G ≤
      normalizedCompactHaarContinuousCentralL2Range G :=
  unitaryMatrixDualL2CharacterAlgebraicRange_le_continuousCentralRange

omit [T2Space G] in
/-- The unconditional direction remains only inclusion of closed spans, not equality. -/
theorem exact_character_closedSpan_inclusion :
    unitaryMatrixDualL2CharacterClosedSpan G ≤
      normalizedCompactHaarContinuousCentralL2ClosedSpan G :=
  unitaryMatrixDualL2CharacterClosedSpan_le_continuousCentralClosedSpan

/-- A future compact-group uniform central-density theorem supplies the exact central `L²` target. -/
theorem exact_continuous_central_to_L2_bridge
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G) :
    UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G :=
  density.hasCentralL2PeterWeylCompleteness

/-- Hostile bridge probe: uniform central density cannot coexist with failed central `L²`
completeness. -/
theorem central_uniform_density_with_failed_L2_blocked
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (failed : ¬ UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G) : False :=
  failed density.hasCentralL2PeterWeylCompleteness

/-- Central `L²` completeness has exact finite-support approximation semantics on the named closed
continuous-central subspace. -/
theorem exact_central_L2_character_approximation
    (complete : UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G)
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖unitaryMatrixDualL2CharacterSynthesis G c - f‖ < ε :=
  complete.exists_character_approximation f hf hε

/-- Hostile approximation probe: one central-span vector with no finite character approximant blocks
central `L²` completeness. -/
theorem missing_central_L2_character_approximation_blocks_completeness
    (f : NormalizedCompactHaarL2 G)
    (hf : f ∈ normalizedCompactHaarContinuousCentralL2ClosedSpan G)
    {ε : ℝ} (hε : 0 < ε)
    (missing : ∀ c : UnitaryMatrixDualCharacterCoefficients G,
      ε ≤ ‖unitaryMatrixDualL2CharacterSynthesis G c - f‖) :
    ¬ UnitaryMatrixDual.HasCentralL2PeterWeylCompleteness G := by
  intro complete
  rcases complete.exists_character_approximation f hf hε with ⟨c, hc⟩
  exact (not_lt_of_ge (missing c)) hc

end

end Probes
end UnitaryMatrixDualCentralL2Span
end Mathematics
end YangMills
