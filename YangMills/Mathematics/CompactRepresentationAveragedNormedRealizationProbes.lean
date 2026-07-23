/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactRepresentationAveragedNormedRealization

/-!
# Hostile probes for the averaged normed realization
-/

namespace YangMills
namespace Mathematics
namespace CompactRepresentationAveragedNormedRealization
namespace Probes

noncomputable section

universe uG

variable
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)

/-- The named normed realization retains the original coordinate topology definitionally. -/
theorem exact_named_norm_topology :
    (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Fin n → ℂ)) := by
  rfl

/-- The normed-space structure inherited from the named inner-product realization is exactly the
separately exposed named normed-space value. -/
theorem exact_named_normedSpace_coherence :
    compactRepresentationAveragedNormedSpace ρ hρ =
      @InnerProductSpace.toNormedSpace ℂ (Fin n → ℂ) _
        (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
        (compactRepresentationAveragedInnerProductSpace ρ hρ) := by
  rfl

/-- The named inner-product realization evaluates to the unchanged Haar-averaged pairing. -/
theorem exact_named_inner (first second : Fin n → ℂ) :
    @inner ℂ (Fin n → ℂ)
      (@InnerProductSpace.toCore ℂ (Fin n → ℂ) _
        (compactRepresentationAveragedNormedAddCommGroup ρ hρ)
        (compactRepresentationAveragedInnerProductSpace ρ hρ)).toInner first second =
      compactRepresentationAveragedPairing ρ first second :=
  compactRepresentationAveragedInnerProductSpace_inner ρ hρ first second

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Exact action probe: the forward carrier of the linear equivalence is the original
representation matrix action. -/
theorem exact_action_linear_equiv (g : G) (vector : Fin n → ℂ) :
    matrixRepresentationLinearEquiv ρ g vector = Matrix.mulVec (ρ g) vector := by
  rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Exact inverse probe: the inverse carrier is the unchanged representation matrix at `g⁻¹`. -/
theorem exact_action_linear_equiv_inverse (g : G) (vector : Fin n → ℂ) :
    (matrixRepresentationLinearEquiv ρ g).symm vector =
      Matrix.mulVec (ρ (g⁻¹)) vector := by
  rfl

/-- The action preserves the exact named averaged norm, not merely an unrelated equivalent norm. -/
theorem exact_averaged_action_norm (g : G) (vector : Fin n → ℂ) :
    @norm (Fin n → ℂ)
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toNorm
      (Matrix.mulVec (ρ g) vector) =
    @norm (Fin n → ℂ)
      (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toNorm vector :=
  compactRepresentationAveragedAction_norm ρ hρ g vector

/-- Hostile norm probe: changing the exact invariant norm equality is contradictory. -/
theorem changed_averaged_action_norm_blocked
    (g : G) (vector : Fin n → ℂ)
    (changed :
      @norm (Fin n → ℂ)
        (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toNorm
        (Matrix.mulVec (ρ g) vector) ≠
      @norm (Fin n → ℂ)
        (compactRepresentationAveragedNormedAddCommGroup ρ hρ).toNorm vector) : False :=
  changed (compactRepresentationAveragedAction_norm ρ hρ g vector)

/-- Dimension-zero probe: the named normed realization and topology remain available without a
positive-dimension assumption. -/
theorem zero_dimension_named_topology
    (ρ₀ : G →* Matrix (Fin 0) (Fin 0) ℂ) (hρ₀ : Continuous ρ₀) :
    (compactRepresentationAveragedNormedAddCommGroup ρ₀ hρ₀).toMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Fin 0 → ℂ)) := by
  rfl

end

end Probes
end CompactRepresentationAveragedNormedRealization
end Mathematics
end YangMills
