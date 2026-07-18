/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Dimensions
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group

/-!
# Finite periodic lattice gauge fields

Wilson 1974, §III, and Osterwalder–Seiler 1978, pp. 442–443, place compact-group variables on
oriented lattice bonds, transform them at their endpoints, and build the action from plaquette
holonomy conjugacy classes. This module packages the finite periodic combinatorics and proves exact
local gauge covariance/invariance.

The plaquette potential is an explicit conjugation-invariant nonnegative class function. This
includes Wilson-type choices after a representation/trace interpretation is supplied, without
pretending that an arbitrary compact simple group has a canonical matrix trace or normalization.
No Gibbs measure, reflection positivity, continuum limit, confinement, theory, or mass gap is
constructed.
-/

namespace YangMills.Lattice

/-- A nonempty finite periodic lattice, with `edgeParameter + 1` sites on each coordinate axis. -/
structure FinitePeriodicLattice where
  /-- Writing the extent as a successor avoids hidden nonemptiness assumptions. -/
  edgeParameter : ℕ
  deriving DecidableEq

/-- Number of sites on each periodic coordinate axis. -/
def FinitePeriodicLattice.extent (Λ : FinitePeriodicLattice) : ℕ :=
  Λ.edgeParameter + 1

/-- A periodic lattice vertex in dimension `d`. -/
abbrev Vertex (d : EuclideanDimension) (Λ : FinitePeriodicLattice) :=
  d.CoordinateIndex → Fin Λ.extent

/-- A positively oriented bond, based at one vertex and pointing along one coordinate axis. -/
structure PositiveOrientedLink (d : EuclideanDimension) (Λ : FinitePeriodicLattice) where
  base : Vertex d Λ
  direction : d.CoordinateIndex
  deriving DecidableEq, Fintype

/-- Cyclic successor on one nonempty periodic coordinate axis. -/
def cyclicSucc (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) : Fin Λ.extent := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  exact i + 1

/-- Cyclic predecessor on one nonempty periodic coordinate axis. -/
def cyclicPred (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) : Fin Λ.extent := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  exact i - 1

@[simp] theorem cyclicSucc_cyclicPred
    (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) :
    cyclicSucc Λ (cyclicPred Λ i) = i := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  simp [cyclicSucc, cyclicPred]

@[simp] theorem cyclicPred_cyclicSucc
    (Λ : FinitePeriodicLattice) (i : Fin Λ.extent) :
    cyclicPred Λ (cyclicSucc Λ i) = i := by
  letI : NeZero Λ.extent := ⟨by simp [FinitePeriodicLattice.extent]⟩
  simp [cyclicSucc, cyclicPred]

/-- Shift one periodic vertex forward by one lattice unit. -/
def shiftForward
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) (μ : d.CoordinateIndex) : Vertex d Λ :=
  Function.update x μ (cyclicSucc Λ (x μ))

/-- Shift one periodic vertex backward by one lattice unit. -/
def shiftBackward
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) (μ : d.CoordinateIndex) : Vertex d Λ :=
  Function.update x μ (cyclicPred Λ (x μ))

@[simp] theorem shiftForward_shiftBackward
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    shiftForward (shiftBackward x μ) μ = x := by
  funext i
  by_cases hi : i = μ
  · subst i
    simp [shiftForward, shiftBackward]
  · simp [shiftForward, shiftBackward, hi]

@[simp] theorem shiftBackward_shiftForward
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) (μ : d.CoordinateIndex) :
    shiftBackward (shiftForward x μ) μ = x := by
  funext i
  by_cases hi : i = μ
  · subst i
    simp [shiftForward, shiftBackward]
  · simp [shiftForward, shiftBackward, hi]

/-- Shifts in distinct coordinate directions commute. -/
theorem shiftForward_comm
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    shiftForward (shiftForward x μ) ν =
      shiftForward (shiftForward x ν) μ := by
  funext i
  by_cases hiμ : i = μ
  · subst i
    simp [shiftForward, hμν]
  · by_cases hiν : i = ν
    · subst i
      simp [shiftForward, hμν, hiμ]
    · simp [shiftForward, hiμ, hiν]

/-- A finite-cutoff lattice gauge field stores one group element on every positive bond. -/
abbrev GaugeField
    (d : EuclideanDimension) (Λ : FinitePeriodicLattice) (G : Type*) :=
  PositiveOrientedLink d Λ → G

/-- A local lattice gauge transformation assigns one group element to every vertex. -/
abbrev GaugeTransformation
    (d : EuclideanDimension) (Λ : FinitePeriodicLattice) (G : Type*) :=
  Vertex d Λ → G

/-- Exact endpoint action of a local gauge transformation on a positive link. -/
def gaugeTransform
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G) : GaugeField d Λ G :=
  fun link => g link.base * U link * (g (shiftForward link.base link.direction))⁻¹

/-- Positively oriented elementary plaquette holonomy in the ordered `μ,ν` plane. -/
def plaquetteHolonomy
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    (μ ν : d.CoordinateIndex) : G :=
  U ⟨x, μ⟩ * U ⟨shiftForward x μ, ν⟩ *
    (U ⟨shiftForward x ν, μ⟩)⁻¹ * (U ⟨x, ν⟩)⁻¹

/-- Plaquette holonomy transforms by conjugation at its base vertex. -/
theorem plaquetteHolonomy_gaugeTransform
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    plaquetteHolonomy (gaugeTransform g U) x μ ν =
      g x * plaquetteHolonomy U x μ ν * (g x)⁻¹ := by
  have hshift := shiftForward_comm x hμν
  simp only [plaquetteHolonomy, gaugeTransform]
  rw [hshift]
  group

/-- Swapping plaquette directions reverses the oriented holonomy. -/
theorem plaquetteHolonomy_swap
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    (μ ν : d.CoordinateIndex) :
    plaquetteHolonomy U x ν μ = (plaquetteHolonomy U x μ ν)⁻¹ := by
  simp only [plaquetteHolonomy]
  group

/-- An admissible plaquette action density: a normalized, orientation-independent, nontrivial
nonnegative conjugation class function. -/
structure PlaquettePotentialData (G : Type*) [Group G] where
  potential : G → ℝ
  nonnegative : ∀ u, 0 ≤ potential u
  identity_zero : potential 1 = 0
  conjugation_invariant : ∀ g u, potential (g * u * g⁻¹) = potential u
  inversion_invariant : ∀ u, potential u⁻¹ = potential u
  nontrivial : ∃ u, 0 < potential u

/-- The admissible plaquette density is independent of plaquette orientation. -/
theorem PlaquettePotentialData.plaquette_swap
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (μ ν : d.CoordinateIndex) :
    potential.potential (plaquetteHolonomy U x ν μ) =
      potential.potential (plaquetteHolonomy U x μ ν) := by
  rw [plaquetteHolonomy_swap, potential.inversion_invariant]

/-- The nontriviality field blocks the identically-zero plaquette density. -/
theorem PlaquettePotentialData.potential_ne_zero
    {G : Type*} [Group G] (potential : PlaquettePotentialData G) :
    potential.potential ≠ 0 := by
  rcases potential.nontrivial with ⟨u, hu⟩
  intro hzero
  have := congrFun hzero u
  simp at this
  linarith

/-- Strictly positive finite-cutoff action coefficient. -/
structure LatticeCouplingData where
  coefficient : ℝ
  positive : 0 < coefficient

/-- Finite periodic Wilson-type action, summing each coordinate plaquette orientation once. -/
noncomputable def wilsonTypeLatticeAction
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    {G : Type*} [Group G] (potential : PlaquettePotentialData G)
    (coupling : LatticeCouplingData) (U : GaugeField d Λ G) : ℝ :=
  coupling.coefficient *
    ∑ x : Vertex d Λ, ∑ μ : d.CoordinateIndex,
      ∑ ν ∈ Finset.univ.filter (fun ν : d.CoordinateIndex => μ < ν),
        potential.potential (plaquetteHolonomy U x μ ν)

/-- The Wilson-type finite-cutoff action is exactly gauge invariant. -/
theorem wilsonTypeLatticeAction_gaugeInvariant
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    {G : Type*} [Group G] (potential : PlaquettePotentialData G)
    (coupling : LatticeCouplingData) (g : GaugeTransformation d Λ G)
    (U : GaugeField d Λ G) :
    wilsonTypeLatticeAction Λ potential coupling (gaugeTransform g U) =
      wilsonTypeLatticeAction Λ potential coupling U := by
  unfold wilsonTypeLatticeAction
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν hν
  rw [Finset.mem_filter] at hν
  rw [plaquetteHolonomy_gaugeTransform g U x (ne_of_lt hν.2)]
  exact potential.conjugation_invariant (g x) _

/-- The identity gauge field has identity plaquette holonomy. -/
@[simp] theorem plaquetteHolonomy_identity
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (x : Vertex d Λ) (μ ν : d.CoordinateIndex) :
    plaquetteHolonomy (fun _ : PositiveOrientedLink d Λ => (1 : G)) x μ ν = 1 := by
  simp [plaquetteHolonomy]

/-- The identity gauge field has zero Wilson-type action. -/
@[simp] theorem wilsonTypeLatticeAction_identity
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    {G : Type*} [Group G] (potential : PlaquettePotentialData G)
    (coupling : LatticeCouplingData) :
    wilsonTypeLatticeAction Λ potential coupling
      (fun _ : PositiveOrientedLink d Λ => (1 : G)) = 0 := by
  simp [wilsonTypeLatticeAction, potential.identity_zero]

/-- Positive coupling and a nonnegative plaquette potential give a nonnegative finite action. -/
theorem wilsonTypeLatticeAction_nonnegative
    {d : EuclideanDimension} (Λ : FinitePeriodicLattice)
    {G : Type*} [Group G] (potential : PlaquettePotentialData G)
    (coupling : LatticeCouplingData) (U : GaugeField d Λ G) :
    0 ≤ wilsonTypeLatticeAction Λ potential coupling U := by
  unfold wilsonTypeLatticeAction
  apply mul_nonneg coupling.positive.le
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro μ _
  apply Finset.sum_nonneg
  intro ν hν
  exact potential.nonnegative _

/-- Dimension one has no ordered pair of distinct plaquette directions. -/
theorem oneDimensional_no_plaquetteDirections
    (μ ν : EuclideanDimension.one.CoordinateIndex) : ¬ μ < ν := by
  intro h
  fin_cases μ
  fin_cases ν
  simp at h

/-- Consequently every dimension-one Wilson-type plaquette action vanishes, independently of the
link holonomy. -/
theorem oneDimensional_wilsonTypeLatticeAction_zero
    (Λ : FinitePeriodicLattice) {G : Type*} [Group G]
    (potential : PlaquettePotentialData G) (coupling : LatticeCouplingData)
    (U : GaugeField EuclideanDimension.one Λ G) :
    wilsonTypeLatticeAction Λ potential coupling U = 0 := by
  simp [wilsonTypeLatticeAction, oneDimensional_no_plaquetteDirections]

end YangMills.Lattice
