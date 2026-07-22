/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationHaarAverage

/-!
# Hostile probes for compact-representation Haar averaging
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationHaarAverage
namespace Probes

noncomputable section

universe uG

/-- The average is taken along the exact same representation in both arguments. -/
theorem exact_pairing_average
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ first second =
      ∫ g, coordinateHermitianPairing
        (Matrix.mulVec (ρ g) first) (Matrix.mulVec (ρ g) second)
        ∂normalizedCompactHaarMeasure G :=
  rfl

/-- Simultaneous representation transport leaves the exact averaged pairing unchanged. -/
theorem exact_pairing_invariance
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h : G) (first second : Fin n → ℂ) :
    compactRepresentationAveragedPairing ρ
        (Matrix.mulVec (ρ h) first) (Matrix.mulVec (ρ h) second) =
      compactRepresentationAveragedPairing ρ first second :=
  compactRepresentationAveragedPairing_invariant ρ h first second

/-- The real averaged norm square uses the same representation and normalized Haar measure. -/
theorem exact_norm_average
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (vector : Fin n → ℂ) :
    compactRepresentationAveragedNormSq ρ vector =
      ∫ g, ∑ i, Complex.normSq (Matrix.mulVec (ρ g) vector i)
        ∂normalizedCompactHaarMeasure G :=
  rfl

/-- Hostile probe: no nonzero vector can have zero averaged norm square. -/
theorem nonzero_average_cannot_collapse
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (vector : Fin n → ℂ) (hvector : vector ≠ 0) :
    compactRepresentationAveragedNormSq ρ vector ≠ 0 :=
  ne_of_gt (compactRepresentationAveragedNormSq_pos ρ hρ vector hvector)

/-- The positive averaged norm remains exactly representation invariant. -/
theorem exact_norm_invariance
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (h : G) (vector : Fin n → ℂ) :
    compactRepresentationAveragedNormSq ρ (Matrix.mulVec (ρ h) vector) =
      compactRepresentationAveragedNormSq ρ vector :=
  compactRepresentationAveragedNormSq_invariant ρ h vector

end

end Probes
end CompactRepresentationHaarAverage
end Mathematics
end YangMills
