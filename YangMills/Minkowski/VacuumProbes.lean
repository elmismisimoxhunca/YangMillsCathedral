/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.Vacuum

/-!
# Hostile probes for the Poincaré-invariant vacuum

Every probe is conditional on supplied representation and vacuum data. The probes force nonzero
normalization, invariance under the same Poincaré and translation representations, and uniqueness of
the full invariant line. No vacuum is constructed.
-/

namespace YangMills.Minkowski.Vacuum.Probes

/-- Unit normalization blocks a zero vacuum. -/
theorem selected_vacuum_ne_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) : vacuumData.vacuum ≠ 0 :=
  vacuumData.vacuum_ne_zero

/-- The same full Poincaré representation fixes the selected vacuum. -/
theorem exact_poincare_invariance
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) (g : G) :
    U.unitary g vacuumData.vacuum = vacuumData.vacuum :=
  vacuumData.invariant g

/-- Physical translations derived from that same representation fix the vacuum. -/
theorem exact_translation_invariance
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) (a : Spacetime d) :
    U.translationUnitary a vacuumData.vacuum = vacuumData.vacuum :=
  vacuumData.translation_invariant a

/-- Every invariant vector lies on the selected vacuum line. -/
theorem invariant_vector_is_vacuum_multiple
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) (ψ : H)
    (hψ : IsPoincareInvariantVector U ψ) :
    ∃ c : ℂ, ψ = c • vacuumData.vacuum :=
  vacuumData.invariant_line ψ hψ

/-- Every normalized invariant vector differs only by a unit-modulus phase. -/
theorem normalized_invariant_is_phase_vacuum
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) (ψ : H)
    (hψnorm : ‖ψ‖ = 1) (hψ : IsPoincareInvariantVector U ψ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ψ = c • vacuumData.vacuum :=
  vacuumData.normalized_invariant_eq_phase_smul ψ hψnorm hψ

/-- A purported invariant vector outside the selected vacuum line is impossible. -/
theorem disconnected_invariant_vector_blocked
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U) (ψ : H)
    (hψ : IsPoincareInvariantVector U ψ)
    (houtside : ∀ c : ℂ, ψ ≠ c • vacuumData.vacuum) : False := by
  rcases vacuumData.invariant_line ψ hψ with ⟨c, hc⟩
  exact houtside c hc

end YangMills.Minkowski.Vacuum.Probes
