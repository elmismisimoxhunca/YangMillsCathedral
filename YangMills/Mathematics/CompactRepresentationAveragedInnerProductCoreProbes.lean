/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationAveragedInnerProductCore

/-!
# Hostile probes for the Haar-averaged inner-product core
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationAveragedInnerProductCore
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)

/-- The packaged core retains the exact averaged pairing. -/
theorem exact_core_pairing (first second : Fin n → ℂ) :
    @inner ℂ (Fin n → ℂ)
      (compactRepresentationAveragedInnerProductCore ρ hρ).toCore.toInner
      first second = compactRepresentationAveragedPairing ρ first second :=
  rfl

omit [T2Space G] in
/-- The core's first-argument scalar law has the exact complex conjugation. -/
theorem exact_conjugate_scalar_law
    (scalar : ℂ) (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ (scalar • first) second =
      star scalar * compactRepresentationAveragedPairing ρ first second :=
  compactRepresentationAveragedPairing_smul_left ρ scalar first second

include hρ in
/-- The real self-pairing is the exact positive averaged norm square. -/
theorem exact_self_pairing_re (vector : Fin n → ℂ) :
    (compactRepresentationAveragedPairing ρ vector vector).re =
      compactRepresentationAveragedNormSq ρ vector :=
  compactRepresentationAveragedPairing_self_re ρ hρ vector

include hρ in
/-- Hostile probe: zero self-pairing forces the original coordinate vector to be zero. -/
theorem self_pairing_zero_forces_zero
    (vector : Fin n → ℂ)
    (selfPairingZero : compactRepresentationAveragedPairing ρ vector vector = 0) :
    vector = 0 := by
  exact (compactRepresentationAveragedInnerProductCore ρ hρ).definite
    vector selfPairingZero

omit [T2Space G] in
/-- The packaged core does not alter the previously derived representation invariance. -/
theorem exact_invariant_core_pairing
    (g : G) (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ
        (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second) =
      compactRepresentationAveragedPairing ρ first second :=
  compactRepresentationAveragedPairing_invariant ρ g first second

end

end Probes
end CompactRepresentationAveragedInnerProductCore
end Mathematics
end YangMills
