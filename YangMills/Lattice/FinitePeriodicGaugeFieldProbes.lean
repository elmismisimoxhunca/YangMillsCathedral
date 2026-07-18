/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FinitePeriodicGaugeField

/-!
# Hostile probes for finite periodic lattice gauge fields

The probes expose nonempty cutoff axes, periodic shifts, exact endpoint gauge action, plaquette
conjugation, action invariance/nonnegativity, identity normalization, and dimension-one absence of
plaquettes. No lattice measure or continuum claim is constructed.
-/

namespace YangMills.Lattice.FinitePeriodicGaugeField.Probes

/-- Every encoded periodic axis has at least one site. -/
theorem extent_positive (Λ : FinitePeriodicLattice) : 0 < Λ.extent := by
  simp [FinitePeriodicLattice.extent]

/-- On the one-site periodic lattice, every forward shift fixes the unique vertex. -/
theorem one_site_shift_is_identity
    (d : EuclideanDimension)
    (x : Vertex d ⟨0⟩) (μ : d.CoordinateIndex) :
    shiftForward x μ = x := by
  funext i
  apply Fin.ext
  have hleft := (shiftForward x μ i).isLt
  have hright := (x i).isLt
  change (shiftForward x μ i).val < 1 at hleft
  change (x i).val < 1 at hright
  omega

/-- Distinct periodic coordinate shifts commute exactly. -/
theorem exact_shift_commutation
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    shiftForward (shiftForward x μ) ν =
      shiftForward (shiftForward x ν) μ :=
  shiftForward_comm x hμν

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]

/-- Link transformation uses exactly its base and forward endpoint. -/
theorem exact_link_gauge_action
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    gaugeTransform g U ⟨x, μ⟩ =
      g x * U ⟨x, μ⟩ * (g (shiftForward x μ))⁻¹ :=
  rfl

/-- Plaquette holonomy transforms by exact base-point conjugation. -/
theorem exact_plaquette_conjugation
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    plaquetteHolonomy (gaugeTransform g U) x μ ν =
      g x * plaquetteHolonomy U x μ ν * (g x)⁻¹ :=
  plaquetteHolonomy_gaugeTransform g U x hμν

/-- The identity field has exact identity plaquette holonomy. -/
theorem exact_identity_plaquette
    (x : Vertex d Λ) (μ ν : d.CoordinateIndex) :
    plaquetteHolonomy (fun _ : PositiveOrientedLink d Λ => (1 : G)) x μ ν = 1 :=
  plaquetteHolonomy_identity x μ ν

/-- Swapping plaquette directions gives inverse holonomy. -/
theorem exact_plaquette_orientation_reversal
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    (μ ν : d.CoordinateIndex) :
    plaquetteHolonomy U x ν μ = (plaquetteHolonomy U x μ ν)⁻¹ :=
  plaquetteHolonomy_swap U x μ ν

/-- The admissible potential is exactly orientation-independent. -/
theorem exact_potential_orientation_independence
    (potential : PlaquettePotentialData G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (μ ν : d.CoordinateIndex) :
    potential.potential (plaquetteHolonomy U x ν μ) =
      potential.potential (plaquetteHolonomy U x μ ν) :=
  potential.plaquette_swap U x μ ν

/-- The potential cannot be the identically-zero class function. -/
theorem zero_potential_blocked (potential : PlaquettePotentialData G) :
    potential.potential ≠ 0 :=
  potential.potential_ne_zero

/-- The finite Wilson-type action is exactly gauge invariant. -/
theorem exact_action_gauge_invariance
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G) :
    wilsonTypeLatticeAction Λ potential coupling (gaugeTransform g U) =
      wilsonTypeLatticeAction Λ potential coupling U :=
  wilsonTypeLatticeAction_gaugeInvariant Λ potential coupling g U

/-- Identity normalization prevents a fake nonzero vacuum action. -/
theorem exact_identity_action_zero
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData) :
    wilsonTypeLatticeAction Λ potential coupling
      (fun _ : PositiveOrientedLink d Λ => (1 : G)) = 0 :=
  wilsonTypeLatticeAction_identity Λ potential coupling

/-- Nonnegative coupling and potential give a nonnegative finite action. -/
theorem exact_action_nonnegative
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField d Λ G) :
    0 ≤ wilsonTypeLatticeAction Λ potential coupling U :=
  wilsonTypeLatticeAction_nonnegative Λ potential coupling U

/-- Dimension two has a genuine ordered coordinate-plane pair. -/
theorem two_dimensional_plaquette_directions_exist :
    ∃ μ ν : EuclideanDimension.two.CoordinateIndex, μ < ν := by
  exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

/-- Dimension one has no ordered coordinate-plane pair. -/
theorem one_dimensional_no_plaquette_directions
    (μ ν : EuclideanDimension.one.CoordinateIndex) : ¬ μ < ν := by
  fin_cases μ
  fin_cases ν
  simp

/-- Consequently every dimension-one Wilson-type plaquette action is zero. -/
theorem one_dimensional_action_zero
    (Λ : FinitePeriodicLattice) (potential : PlaquettePotentialData G)
    (coupling : LatticeCouplingData)
    (U : GaugeField EuclideanDimension.one Λ G) :
    wilsonTypeLatticeAction Λ potential coupling U = 0 := by
  simp [wilsonTypeLatticeAction, one_dimensional_no_plaquette_directions]

end YangMills.Lattice.FinitePeriodicGaugeField.Probes
