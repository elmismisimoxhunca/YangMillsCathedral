/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteLatticeReflectionPositivity

/-!
# Lattice ultraviolet/thermodynamic scaling trajectories

Wilson 1974 motivates taking lattice spacing to zero, while Osterwalder–Seiler 1978, pp. 468–469,
explicitly tunes the bare coupling with the spacing in its two-dimensional continuum discussion.
This module defines an acceptance interface for a simultaneous ultraviolet and infinite-volume
trajectory. It does not assert that such a trajectory exists or converges.

The lattice action coefficient is kept distinct from the bare gauge coupling and connected by an
explicit injective normalization convention. Every cutoff carries its own exact product-Haar Gibbs
data. A separate bridge can require convergence of finite-cutoff gauge-invariant observable
expectations to an independently supplied target functional. This expectation-level bridge does not
identify lattice fields, measures, OS data, Wightman data, or a continuum Yang–Mills theory.
-/

namespace YangMills.Lattice

open Filter MeasureTheory Topology

/-- Strictly positive physical lattice spacing. -/
structure LatticeSpacingData where
  value : ℝ
  positive : 0 < value

/-- Physical linear size of one periodic lattice direction at a given spacing. -/
def latticePhysicalLinearExtent
    (Λ : FinitePeriodicLattice) (spacing : LatticeSpacingData) : ℝ :=
  spacing.value * Λ.extent

/-- Simultaneous ultraviolet, thermodynamic, and bare-coupling scaling data.

No field claims convergence of measures or theories. -/
structure FiniteLatticeScalingTrajectoryData
    (d : EuclideanDimension)
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] where
  /-- Periodic cutoff lattice at stage `n`. -/
  lattice : ℕ → FinitePeriodicLattice
  /-- Positive physical spacing at stage `n`. -/
  spacing : ℕ → LatticeSpacingData
  /-- Stage-dependent plaquette potential; no fixed-potential shortcut is imposed. -/
  potential : ℕ → PlaquettePotentialData G
  /-- Stage-dependent coefficient in the exact lattice action. -/
  actionCoupling : ℕ → LatticeCouplingData
  /-- Stage-dependent bare gauge coupling, kept semantically distinct from the action coefficient. -/
  bareGaugeCoupling : ℕ → ℝ
  bareGaugeCoupling_positive : ∀ n, 0 < bareGaugeCoupling n
  /-- Explicit convention converting bare gauge coupling to the action coefficient. -/
  actionCoefficientFromBareCoupling : ℝ → ℝ
  /-- Injectivity prevents the convention from discarding the bare coupling. -/
  actionCoefficientFromBareCoupling_injective :
    Function.Injective actionCoefficientFromBareCoupling
  actionCoefficientFromBareCoupling_positive : ∀ g, 0 < g →
    0 < actionCoefficientFromBareCoupling g
  /-- Exact normalization coherence at every cutoff. -/
  actionCoefficient_coherence : ∀ n,
    (actionCoupling n).coefficient =
      actionCoefficientFromBareCoupling (bareGaugeCoupling n)
  /-- Exact finite product-Haar Gibbs acceptance data at every cutoff. -/
  gibbs : ∀ n,
    @FiniteProductHaarGibbsMeasureData d (lattice n) G _ _ _ _ _ _
      (potential n) (actionCoupling n)
  /-- Ultraviolet removal. -/
  spacing_tends_zero : Tendsto (fun n => (spacing n).value) atTop (𝓝 0)
  /-- The number of sites per axis cannot remain at a fixed finite cutoff. -/
  extent_tends_atTop : Tendsto (fun n => (lattice n).extent) atTop atTop
  /-- Physical linear extent diverges while the spacing vanishes. -/
  physical_extent_tends_atTop :
    Tendsto (fun n => latticePhysicalLinearExtent (lattice n) (spacing n)) atTop atTop
  /-- Weak-bare-coupling scaling obligation. This is only a regulator trajectory condition, not a
  proof of continuum asymptotic freedom. -/
  bareGaugeCoupling_tends_zero : Tendsto bareGaugeCoupling atTop (𝓝 0)

/-- Exact finite-cutoff expectation along one scaling trajectory. -/
noncomputable def scalingTrajectoryExpectation
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (n : ℕ)
    (observable : @FiniteSupportedGaugeInvariantLatticeObservable d
      (trajectory.lattice n) G _ _) : ℂ :=
  finiteLatticeExpectation (trajectory.gibbs n).toFiniteLatticeGibbsMeasureData
    observable.observable

/-- Expectation-level bridge from exact finite lattice observables to an independently supplied
continuum observable functional.

The target carrier and functional are parameters, not constructed or identified with OS/Wightman
objects here. -/
structure LatticeToContinuumObservableExpectationBridgeData
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (ContinuumObservable : Type*)
    (continuumExpectation : ContinuumObservable → ℂ) where
  /-- Exact lattice approximant at every cutoff for every independently supplied target observable. -/
  latticeApproximation : ∀ n, ContinuumObservable →
    @FiniteSupportedGaugeInvariantLatticeObservable d (trajectory.lattice n) G _ _
  /-- Convergence is required; it is never obtained by definitional identification. -/
  expectation_converges : ∀ O,
    Tendsto (fun n => scalingTrajectoryExpectation trajectory n (latticeApproximation n O))
      atTop (𝓝 (continuumExpectation O))
  /-- Distinguished normalized target unit. -/
  unitObservable : ContinuumObservable
  continuumExpectation_unit : continuumExpectation unitObservable = 1
  /-- Every lattice approximant to the unit is exactly the constant-one observable. -/
  latticeApproximation_unit : ∀ n,
    (latticeApproximation n unitObservable).observable.toFun = fun _ => 1
  /-- A separate target observable has genuine one-link dependence at every cutoff, blocking a
  bridge consisting only of constant functions. -/
  nontrivialObservable : ContinuumObservable
  nontrivial_lattice_dependence : ∀ n,
    ∃ link : PositiveOrientedLink d (trajectory.lattice n),
      DependsNontriviallyOnLink (latticeApproximation n nontrivialObservable) link

end YangMills.Lattice
