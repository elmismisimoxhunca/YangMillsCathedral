/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationCompleteReducibility

/-!
# Hostile probes for compact-representation complete reducibility
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationCompleteReducibility
namespace Probes

open scoped MonoidAlgebra

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)

/-- Membership uses the exact Haar-averaged pairing rather than an unrelated inner product. -/
theorem exact_complement_membership
    (subrepresentation : Subrepresentation (matrixRepresentation ρ))
    (vector : Fin n → ℂ) :
    vector ∈ compactRepresentationOrthogonalComplement ρ hρ subrepresentation ↔
      ∀ subspaceVector ∈ subrepresentation,
        compactRepresentationAveragedPairing ρ vector subspaceVector = 0 :=
  mem_compactRepresentationOrthogonalComplement_iff ρ hρ subrepresentation vector

/-- The orthogonal complement is invariant under every unchanged representation matrix. -/
theorem exact_complement_invariance
    (subrepresentation : Subrepresentation (matrixRepresentation ρ))
    (g : G) (vector : Fin n → ℂ)
    (orthogonal : vector ∈
      compactRepresentationOrthogonalComplement ρ hρ subrepresentation) :
    Matrix.mulVec (ρ g) vector ∈
      compactRepresentationOrthogonalComplement ρ hρ subrepresentation :=
  (compactRepresentationOrthogonalComplement ρ hρ subrepresentation).apply_mem_toSubmodule
    g orthogonal

/-- The original subrepresentation and its invariant complement have zero intersection. -/
theorem exact_complement_disjoint
    (subrepresentation : Subrepresentation (matrixRepresentation ρ)) :
    Disjoint subrepresentation
      (compactRepresentationOrthogonalComplement ρ hρ subrepresentation) :=
  (compactRepresentationOrthogonalComplement_isCompl ρ hρ subrepresentation).disjoint

/-- The original subrepresentation and its invariant complement span the whole representation. -/
theorem exact_complement_spans
    (subrepresentation : Subrepresentation (matrixRepresentation ρ)) :
    subrepresentation ⊔ compactRepresentationOrthogonalComplement ρ hρ subrepresentation = ⊤ :=
  (compactRepresentationOrthogonalComplement_isCompl ρ hρ subrepresentation).codisjoint.eq_top

include hρ in
/-- Hostile probe: no invariant subrepresentation can fail to have any complement. -/
theorem missing_all_complements_blocked
    (subrepresentation : Subrepresentation (matrixRepresentation ρ))
    (missing : ∀ complement : Subrepresentation (matrixRepresentation ρ),
      ¬ IsCompl subrepresentation complement) : False :=
  missing (compactRepresentationOrthogonalComplement ρ hρ subrepresentation)
    (compactRepresentationOrthogonalComplement_isCompl ρ hρ subrepresentation)

include hρ in
/-- The complete-reducibility theorem exposes Mathlib's exact semisimplicity proposition. -/
theorem exact_semisimplicity :
    Representation.IsSemisimpleRepresentation (matrixRepresentation ρ) :=
  compactRepresentation_isSemisimple ρ hρ

include hρ in
/-- Hostile probe: denying semisimplicity contradicts the constructed invariant complements. -/
theorem nonsemisimplicity_blocked
    (notSemisimple :
      ¬ Representation.IsSemisimpleRepresentation (matrixRepresentation ρ)) : False :=
  notSemisimple (compactRepresentation_isSemisimple ρ hρ)

include hρ in
/-- The resulting group-algebra decomposition is finite and every selected summand is simple. -/
theorem exact_finite_simple_decomposition :
    ∃ (summandCount : ℕ)
      (summands : Fin summandCount →
        Submodule ℂ[G] (matrixRepresentation ρ).asModule)
      (_ : (matrixRepresentation ρ).asModule ≃ₗ[ℂ[G]]
        Π₀ index : Fin summandCount, summands index),
      ∀ index, IsSimpleModule ℂ[G] (summands index) :=
  compactRepresentation_exists_finite_simple_groupAlgebra_decomposition ρ hρ

/-- Dimension zero remains covered; no positive-dimension hypothesis is hidden in semisimplicity. -/
theorem zero_dimension_semisimple
    (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀) :
    Representation.IsSemisimpleRepresentation (matrixRepresentation ρ₀) :=
  compactRepresentation_isSemisimple ρ₀ hρ₀

end

end Probes
end CompactRepresentationCompleteReducibility
end Mathematics
end YangMills
