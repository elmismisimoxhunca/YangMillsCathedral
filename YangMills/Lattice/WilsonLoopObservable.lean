/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FinitePeriodicGaugeField

/-!
# Finite lattice paths and Wilson-loop observables

Wilson 1974 organizes gauge-invariant quantities by ordered lattice paths and closed loops.
Osterwalder–Seiler 1978 treats finitely supported gauge-invariant bond observables. This module
constructs signed lattice paths, exact ordered holonomy, endpoint gauge covariance, and closed-loop
class-function observables. The elementary plaquette path is proved closed and its path holonomy is
proved equal to the existing plaquette holonomy.

No representation trace is chosen canonically: a nontrivial conjugation-invariant class function is
explicit data. No Gibbs expectation, area law, confinement, reflection positivity, continuum limit,
or continuum observable interpretation is asserted.
-/

namespace YangMills.Lattice

/-- One signed lattice step in a coordinate direction. -/
inductive SignedDirection (d : EuclideanDimension) where
  | forward (direction : d.CoordinateIndex)
  | backward (direction : d.CoordinateIndex)
  deriving DecidableEq

/-- Endpoint after traversing one signed lattice step. -/
def stepEndpoint
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) : SignedDirection d → Vertex d Λ
  | .forward μ => shiftForward x μ
  | .backward μ => shiftBackward x μ

/-- Link variable seen along one signed traversal; backward traversal uses the inverse positive
link based at the preceding vertex. -/
def orientedLinkValue
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (U : GaugeField d Λ G) (x : Vertex d Λ) : SignedDirection d → G
  | .forward μ => U ⟨x, μ⟩
  | .backward μ => (U ⟨shiftBackward x μ, μ⟩)⁻¹

/-- One signed link value transforms at its traversal start and endpoint. -/
theorem orientedLinkValue_gaugeTransform
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (step : SignedDirection d) :
    orientedLinkValue (gaugeTransform g U) x step =
      g x * orientedLinkValue U x step * (g (stepEndpoint x step))⁻¹ := by
  cases step with
  | forward μ => rfl
  | backward μ =>
      simp [orientedLinkValue, gaugeTransform, stepEndpoint]
      group

/-- Endpoint of a finite signed path. -/
def pathEndpoint
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} :
    Vertex d Λ → List (SignedDirection d) → Vertex d Λ
  | x, [] => x
  | x, step :: path => pathEndpoint (stepEndpoint x step) path

/-- Ordered group holonomy along a finite signed path. -/
def pathHolonomy
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (U : GaugeField d Λ G) : Vertex d Λ → List (SignedDirection d) → G
  | _, [] => 1
  | x, step :: path =>
      orientedLinkValue U x step * pathHolonomy U (stepEndpoint x step) path

/-- Path holonomy transforms only at the path's initial and final endpoints. -/
theorem pathHolonomy_gaugeTransform
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    pathHolonomy (gaugeTransform g U) x path =
      g x * pathHolonomy U x path * (g (pathEndpoint x path))⁻¹ := by
  induction path generalizing x with
  | nil => simp [pathHolonomy, pathEndpoint]
  | cons step path ih =>
      simp only [pathHolonomy, pathEndpoint]
      rw [orientedLinkValue_gaugeTransform, ih]
      group

/-- A path is closed when its exact periodic endpoint equals its starting vertex. -/
def IsClosedPath
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) (path : List (SignedDirection d)) : Prop :=
  pathEndpoint x path = x

/-- Nontrivial conjugation-invariant function used to interpret closed-loop holonomy. -/
structure GaugeInvariantClassObservable (G : Type*) [Group G] where
  observable : G → ℂ
  conjugation_invariant : ∀ g u, observable (g * u * g⁻¹) = observable u
  nontrivial : ∃ u, observable u ≠ observable 1

/-- Wilson-loop observable associated with one based signed path. -/
def wilsonLoopObservable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (χ : GaugeInvariantClassObservable G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) : ℂ :=
  χ.observable (pathHolonomy U x path)

/-- Every closed-loop observable is exactly invariant under local lattice gauge transformations. -/
theorem wilsonLoopObservable_gaugeInvariant
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (χ : GaugeInvariantClassObservable G) (g : GaugeTransformation d Λ G)
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    (path : List (SignedDirection d)) (hclosed : IsClosedPath x path) :
    wilsonLoopObservable χ (gaugeTransform g U) x path =
      wilsonLoopObservable χ U x path := by
  unfold wilsonLoopObservable
  rw [pathHolonomy_gaugeTransform, hclosed]
  exact χ.conjugation_invariant (g x) _

/-- Signed boundary path of the elementary ordered `μ,ν` plaquette. -/
def plaquettePath
    {d : EuclideanDimension} (μ ν : d.CoordinateIndex) : List (SignedDirection d) :=
  [.forward μ, .forward ν, .backward μ, .backward ν]

/-- The elementary plaquette path closes whenever the two coordinate directions are distinct. -/
theorem plaquettePath_closed
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    IsClosedPath x (plaquettePath μ ν) := by
  change shiftBackward
    (shiftBackward (shiftForward (shiftForward x μ) ν) μ) ν = x
  rw [shiftForward_comm x hμν, shiftBackward_shiftForward,
    shiftBackward_shiftForward]

/-- Path holonomy around the elementary plaquette is exactly the existing plaquette holonomy. -/
theorem pathHolonomy_plaquettePath
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} {G : Type*} [Group G]
    (U : GaugeField d Λ G) (x : Vertex d Λ)
    {μ ν : d.CoordinateIndex} (hμν : μ ≠ ν) :
    pathHolonomy U x (plaquettePath μ ν) = plaquetteHolonomy U x μ ν := by
  simp only [plaquettePath, pathHolonomy, orientedLinkValue, stepEndpoint, mul_one]
  rw [shiftForward_comm x hμν, shiftBackward_shiftForward,
    shiftBackward_shiftForward]
  unfold plaquetteHolonomy
  group

end YangMills.Lattice
