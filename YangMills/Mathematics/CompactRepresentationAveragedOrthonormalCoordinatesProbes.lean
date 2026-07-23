/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationAveragedOrthonormalCoordinates

/-!
# Hostile probes for averaged orthonormal coordinates
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationAveragedOrthonormalCoordinates
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)

/-- Each selected averaged orthonormal basis vector has the exact corresponding Kronecker
coordinate. -/
theorem exact_basis_coordinate (index : Fin n) :
    compactRepresentationUnitarizingLinearEquiv ρ hρ
        (compactRepresentationAveragedOrthonormalBasis ρ hρ index) =
      Pi.single index 1 :=
  compactRepresentationUnitarizingLinearEquiv_apply_basis ρ hρ index

/-- The inverse coordinate equivalence recovers each exact selected basis vector. -/
theorem exact_coordinate_inverse (index : Fin n) :
    (compactRepresentationUnitarizingLinearEquiv ρ hρ).symm (Pi.single index 1) =
      compactRepresentationAveragedOrthonormalBasis ρ hρ index := by
  apply (compactRepresentationUnitarizingLinearEquiv ρ hρ).injective
  simp only [LinearEquiv.apply_symm_apply]
  exact (compactRepresentationUnitarizingLinearEquiv_apply_basis ρ hρ index).symm

/-- Pairing transport uses the exact selected equivalence and the unchanged averaged pairing. -/
theorem exact_unitarizing_pairing (first second : Fin n → ℂ) :
    coordinateHermitianPairing
        (compactRepresentationUnitarizingLinearEquiv ρ hρ first)
        (compactRepresentationUnitarizingLinearEquiv ρ hρ second) =
      compactRepresentationAveragedPairing ρ first second :=
  compactRepresentationUnitarizingLinearEquiv_pairing ρ hρ first second

/-- Hostile pairing probe: changing the exact pairing transported by the selected coordinate
equivalence is contradictory. -/
theorem changed_unitarizing_pairing_blocked
    (first second : Fin n → ℂ)
    (changed : coordinateHermitianPairing
        (compactRepresentationUnitarizingLinearEquiv ρ hρ first)
        (compactRepresentationUnitarizingLinearEquiv ρ hρ second) ≠
      compactRepresentationAveragedPairing ρ first second) : False :=
  changed (compactRepresentationUnitarizingLinearEquiv_pairing ρ hρ first second)

/-- Anti-collapse probe: the coordinate equivalence cannot send a nonzero vector to zero. -/
theorem nonzero_coordinate_image
    (vector : Fin n → ℂ) (vector_ne : vector ≠ 0) :
    compactRepresentationUnitarizingLinearEquiv ρ hρ vector ≠ 0 := by
  exact fun collapsed => vector_ne
    ((compactRepresentationUnitarizingLinearEquiv ρ hρ).map_eq_zero_iff.mp collapsed)

/-- Dimension-zero probe: the coordinate equivalence is still constructed without a positive
matrix-dimension premise. -/
theorem zero_dimension_coordinate_roundtrip
    (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀)
    (vector : Fin 0 → ℂ) :
    (compactRepresentationUnitarizingLinearEquiv ρ₀ hρ₀).symm
        (compactRepresentationUnitarizingLinearEquiv ρ₀ hρ₀ vector) = vector :=
  (compactRepresentationUnitarizingLinearEquiv ρ₀ hρ₀).left_inv vector

end

end Probes
end CompactRepresentationAveragedOrthonormalCoordinates
end Mathematics
end YangMills
