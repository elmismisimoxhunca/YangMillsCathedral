/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualContinuousDensity
import YangMills.Mathematics.UnitaryMatrixDualCharacters

/-!
# Continuous central functions and the character-density target

This file packages conjugation-invariant complex continuous functions on a topological group as a
`StarSubalgebra ℂ C(G, ℂ)`. Finite-support synthesis over quotient-selected irreducible characters is
then bundled first in `C(G, ℂ)` and then in this exact central-function carrier.

The proposition `UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G` states exactly that
finite character synthesis is uniformly dense among continuous central functions. This is the
continuous central Peter–Weyl/character-completeness target used by compact-group heat-kernel
expansions.

No inhabitant of the general target is constructed here. In particular, full coefficient density is
not silently treated as central character density, and no infinite character series or pointwise
inversion is asserted.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- The star subalgebra of complex continuous functions invariant under every inner conjugation. -/
def continuousCentralFunctionStarSubalgebra
    (G : Type uG) [Group G] [TopologicalSpace G] : StarSubalgebra ℂ C(G, ℂ) where
  carrier := {f | ∀ g h : G, f (h * g * h⁻¹) = f g}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro f k hf hk g h
    simp [hf g h, hk g h]
  mul_mem' := by
    intro f k hf hk g h
    simp [hf g h, hk g h]
  algebraMap_mem' := by
    intro c g h
    simp
  star_mem' := by
    intro f hf g h
    simp [hf g h]

/-- Membership in the central-function star subalgebra is exactly pointwise invariance under
`g ↦ h*g*h⁻¹`. -/
theorem mem_continuousCentralFunctionStarSubalgebra_iff
    {G : Type uG} [Group G] [TopologicalSpace G] (f : C(G, ℂ)) :
    f ∈ continuousCentralFunctionStarSubalgebra G ↔
      ∀ g h : G, f (h * g * h⁻¹) = f g :=
  Iff.rfl

/-- Finite-support quotient-dual character synthesis bundled in the continuous-function carrier. -/
noncomputable def unitaryMatrixDualContinuousCharacterSynthesis
    (G : Type uG) [Group G] [TopologicalSpace G] :
    UnitaryMatrixDualCharacterCoefficients G →ₗ[ℂ] C(G, ℂ) where
  toFun c := ⟨unitaryMatrixDualCharacterSynthesis G c,
    continuous_unitaryMatrixDualCharacterSynthesis c⟩
  map_add' c d := by
    ext g
    exact congrFun (map_add (unitaryMatrixDualCharacterSynthesis G) c d) g
  map_smul' a c := by
    ext g
    exact congrFun (map_smul (unitaryMatrixDualCharacterSynthesis G) a c) g

/-- Finite-support quotient-dual character synthesis with codomain restricted to the exact central
continuous-function star subalgebra. -/
noncomputable def unitaryMatrixDualCentralCharacterSynthesis
    (G : Type uG) [Group G] [TopologicalSpace G] :
    UnitaryMatrixDualCharacterCoefficients G →ₗ[ℂ]
      continuousCentralFunctionStarSubalgebra G where
  toFun c := ⟨unitaryMatrixDualContinuousCharacterSynthesis G c,
    unitaryMatrixDualCharacterSynthesis_conj c⟩
  map_add' c d := by
    apply Subtype.ext
    exact map_add (unitaryMatrixDualContinuousCharacterSynthesis G) c d
  map_smul' a c := by
    apply Subtype.ext
    exact map_smul (unitaryMatrixDualContinuousCharacterSynthesis G) a c

/-- The restricted central character synthesis has exactly the original finite character sum at
every group element. -/
@[simp]
theorem unitaryMatrixDualCentralCharacterSynthesis_apply
    {G : Type uG} [Group G] [TopologicalSpace G]
    (c : UnitaryMatrixDualCharacterCoefficients G) (g : G) :
    ((unitaryMatrixDualCentralCharacterSynthesis G c :
      continuousCentralFunctionStarSubalgebra G) : C(G, ℂ)) g =
      unitaryMatrixDualCharacterSynthesis G c g :=
  rfl

/-- Character synthesis into the central continuous carrier remains injective. -/
theorem unitaryMatrixDualCentralCharacterSynthesis_injective
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    Function.Injective (unitaryMatrixDualCentralCharacterSynthesis G) := by
  intro c d hcd
  apply unitaryMatrixDualCharacterSynthesis_injective
  funext g
  exact congrArg (fun f : continuousCentralFunctionStarSubalgebra G => (f : C(G, ℂ)) g) hcd

/-- General continuous central Peter–Weyl target: finite-support selected characters are uniformly
dense in the exact continuous central-function carrier. -/
def UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity
    (G : Type uG) [Group G] [TopologicalSpace G] [CompactSpace G] : Prop :=
  DenseRange (unitaryMatrixDualCentralCharacterSynthesis G)

/-- The central density target gives an arbitrarily accurate finite character approximation to each
continuous central function. This is still a one-approximant-at-a-time statement, not a series. -/
theorem UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity.exists_character_approximation
    {G : Type uG} [Group G] [TopologicalSpace G] [CompactSpace G]
    (density : UnitaryMatrixDual.HasCentralContinuousPeterWeylDensity G)
    (f : continuousCentralFunctionStarSubalgebra G) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : UnitaryMatrixDualCharacterCoefficients G,
      ‖(unitaryMatrixDualCentralCharacterSynthesis G c : C(G, ℂ)) - (f : C(G, ℂ))‖ < ε := by
  change DenseRange (unitaryMatrixDualCentralCharacterSynthesis G) at density
  rcases density.exists_dist_lt f hε with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rwa [← dist_eq_norm, dist_comm]

end

end Mathematics
end YangMills
