/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryCharacterOrthogonality

/-!
# Hostile probes for compact irreducible character orthogonality
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryCharacterOrthogonality
namespace Probes

noncomputable section

universe uG

/-- Every represented irreducible positive-dimensional unitary character has exact normalized norm
one. -/
theorem exact_character_norm_one
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (unitaryρ : ∀ g, star (ρ g) * ρ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    (∫ g, star (Matrix.trace (ρ g)) * Matrix.trace (ρ g)
      ∂normalizedCompactHaarMeasure G) = 1 :=
  normalizedCompactHaar_character_normSq_integral
    ρ hρ unitaryρ dimension_pos

/-- Inequivalent represented irreducible unitary characters have exact zero pairing. -/
theorem exact_inequivalent_character_pairing
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))] :
    (∫ g, star (Matrix.trace (σ g)) * Matrix.trace (ρ g)
      ∂normalizedCompactHaarMeasure G) = 0 :=
  normalizedCompactHaar_character_orthogonality_inequivalent
    σ ρ hσ hρ unitaryσ

/-- Hostile probe: a claimed nonzero inequivalent character pairing is impossible. -/
theorem nonzero_inequivalent_character_pairing_blocked
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {m n : ℕ}
    (σ : G →* Matrix (Fin m) (Fin m) ℂ)
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hσ : Continuous σ) (hρ : Continuous ρ)
    (unitaryσ : ∀ g, star (σ g) * σ g = 1)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    [Representation.IsIrreducible (matrixRepresentation σ)]
    [IsEmpty (Representation.Equiv
      (matrixRepresentation ρ) (matrixRepresentation σ))]
    (claimedNonzero :
      (∫ g, star (Matrix.trace (σ g)) * Matrix.trace (ρ g)
        ∂normalizedCompactHaarMeasure G) ≠ 0) : False :=
  claimedNonzero
    (normalizedCompactHaar_character_orthogonality_inequivalent
      σ ρ hσ hρ unitaryσ)

end

end Probes
end CompactUnitaryCharacterOrthogonality
end Mathematics
end YangMills
