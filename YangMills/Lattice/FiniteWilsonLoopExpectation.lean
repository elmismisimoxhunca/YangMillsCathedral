/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteProductHaarGibbsMeasure
import YangMills.Lattice.WilsonLoopObservable

/-!
# Finitely supported measurable Wilson-loop expectations

Osterwalder–Seiler 1978, pp. 442–443, defines local observables as bounded measurable functions
depending on finitely many bond variables and singles out gauge invariance. This module gives every
finite signed path its exact positive-link support, proves holonomy depends only on that support,
and packages bounded measurable class functions as genuinely integrable finite-product-Haar Gibbs
observables.

An expectation is only a function of supplied `FiniteProductHaarGibbsMeasureData`; no such datum,
numerical expectation, area law, reflection positivity, confinement statement, continuum
interpretation, or mass gap is constructed.
-/

namespace YangMills.Lattice

open MeasureTheory

/-- Positive link read by one signed traversal. -/
def orientedStepPositiveLink
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    (x : Vertex d Λ) : SignedDirection d → PositiveOrientedLink d Λ
  | .forward μ => ⟨x, μ⟩
  | .backward μ => ⟨shiftBackward x μ, μ⟩

/-- Exact finite set of positive links read by a based signed path. -/
def pathLinkSupport
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice} :
    Vertex d Λ → List (SignedDirection d) → Finset (PositiveOrientedLink d Λ)
  | _, [] => ∅
  | x, step :: path =>
      insert (orientedStepPositiveLink x step)
        (pathLinkSupport (stepEndpoint x step) path)

/-- Agreement on the one positive link read by a step gives equal oriented values. -/
theorem orientedLinkValue_eq_of_eq_on_stepLink
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (U V : GaugeField d Λ G) (x : Vertex d Λ) (step : SignedDirection d)
    (h : U (orientedStepPositiveLink x step) =
      V (orientedStepPositiveLink x step)) :
    orientedLinkValue U x step = orientedLinkValue V x step := by
  cases step <;> simpa [orientedStepPositiveLink, orientedLinkValue] using h

/-- Path holonomy depends only on its exact finite positive-link support. -/
theorem pathHolonomy_eq_of_eq_on_pathLinkSupport
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G]
    (U V : GaugeField d Λ G) (x : Vertex d Λ)
    (path : List (SignedDirection d))
    (h : ∀ link ∈ pathLinkSupport x path, U link = V link) :
    pathHolonomy U x path = pathHolonomy V x path := by
  induction path generalizing x with
  | nil => rfl
  | cons step path ih =>
      rw [pathHolonomy, pathHolonomy]
      congr 1
      · apply orientedLinkValue_eq_of_eq_on_stepLink
        exact h _ (by simp [pathLinkSupport])
      · apply ih
        intro link hlink
        exact h link (by simp [pathLinkSupport, hlink])

/-- Measurability of one signed link evaluation on product configuration space. -/
theorem orientedLinkValue_measurable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    (x : Vertex d Λ) (step : SignedDirection d) :
    Measurable (fun U : GaugeField d Λ G => orientedLinkValue U x step) := by
  cases step with
  | forward μ =>
      exact measurable_pi_apply (⟨x, μ⟩ : PositiveOrientedLink d Λ)
  | backward μ =>
      exact (measurable_pi_apply
        (⟨shiftBackward x μ, μ⟩ : PositiveOrientedLink d Λ)).inv

/-- Finite path holonomy is measurable when multiplication and inversion are measurable. -/
theorem pathHolonomy_measurable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    Measurable (fun U : GaugeField d Λ G => pathHolonomy U x path) := by
  induction path generalizing x with
  | nil => exact measurable_const
  | cons step path ih =>
      exact (orientedLinkValue_measurable x step).mul (ih (stepEndpoint x step))

/-- Nonconstant conjugation-class interpretation with the exact `L∞`-style evidence needed for a
finite-cutoff local observable. -/
structure BoundedMeasurableGaugeInvariantClassObservable
    (G : Type*) [Group G] [MeasurableSpace G]
    extends GaugeInvariantClassObservable G where
  observable_measurable : Measurable observable
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  norm_le : ∀ u, ‖observable u‖ ≤ bound

/-- A bounded measurable class interpretation gives a packaged finite lattice observable. -/
def finiteWilsonLoopObservable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d)) :
    @FiniteLatticeObservable d Λ G _ _ where
  toFun := fun U => wilsonLoopObservable χ.toGaugeInvariantClassObservable U x path
  measurable := χ.observable_measurable.comp (pathHolonomy_measurable x path)
  bound := χ.bound
  bound_nonnegative := χ.bound_nonnegative
  norm_le := fun U => χ.norm_le (pathHolonomy U x path)

/-- The packaged observable still depends only on the exact finite path support. -/
theorem finiteWilsonLoopObservable_eq_of_eq_on_pathLinkSupport
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (U V : GaugeField d Λ G) (x : Vertex d Λ)
    (path : List (SignedDirection d))
    (h : ∀ link ∈ pathLinkSupport x path, U link = V link) :
    finiteWilsonLoopObservable χ x path U = finiteWilsonLoopObservable χ x path V := by
  simpa [finiteWilsonLoopObservable, wilsonLoopObservable] using congrArg χ.observable
    (pathHolonomy_eq_of_eq_on_pathLinkSupport U V x path h)

/-- On a closed path, the packaged bounded measurable observable is exactly gauge invariant. -/
theorem finiteWilsonLoopObservable_gaugeInvariant
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (g : GaugeTransformation d Λ G) (U : GaugeField d Λ G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (hclosed : IsClosedPath x path) :
    finiteWilsonLoopObservable χ x path (gaugeTransform g U) =
      finiteWilsonLoopObservable χ x path U := by
  simpa [finiteWilsonLoopObservable] using
    wilsonLoopObservable_gaugeInvariant χ.toGaugeInvariantClassObservable g U x path hclosed

/-- Exact finite-product-Haar Gibbs expectation of one supplied closed Wilson-loop observable.

The closure proof is part of the interface so this name cannot be used for an open-path observable. -/
noncomputable def finiteProductHaarWilsonLoopExpectation
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableMul₂ G] [MeasurableInv G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (χ : BoundedMeasurableGaugeInvariantClassObservable G)
    (x : Vertex d Λ) (path : List (SignedDirection d))
    (_hclosed : IsClosedPath x path) : ℂ :=
  finiteLatticeExpectation data.toFiniteLatticeGibbsMeasureData
    (finiteWilsonLoopObservable χ x path)

end YangMills.Lattice
