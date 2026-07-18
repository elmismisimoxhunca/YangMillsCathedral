/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.LatticeScalingTrajectory

/-!
# Hostile probes for lattice scaling trajectories

The probes reject fixed spacing, bounded sites per axis, bounded physical linear extent, constant positive bare
coupling, discarded normalization conventions, constant-only observable bridges, and unrelated
claimed limits. They construct no trajectory or continuum target.
-/

namespace YangMills.Lattice.LatticeScalingTrajectory.Probes

open Filter Topology

variable
    {d : EuclideanDimension}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- A strictly positive fixed spacing cannot satisfy ultraviolet removal. -/
theorem fixed_positive_spacing_blocked
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (a : ℝ) (ha : 0 < a)
    (hfixed : ∀ n, (trajectory.spacing n).value = a) : False := by
  have hconst : Tendsto (fun n : ℕ => (trajectory.spacing n).value) atTop (𝓝 a) := by
    simpa only [hfixed] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))
  have hazero : a = 0 := tendsto_nhds_unique hconst trajectory.spacing_tends_zero
  linarith

/-- A uniformly bounded number of sites cannot pass the thermodynamic-cutoff condition. -/
theorem bounded_extent_blocked
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (M : ℕ) (hbounded : ∀ n, (trajectory.lattice n).extent ≤ M) : False := by
  have hev : ∀ᶠ n in atTop, M + 1 ≤ (trajectory.lattice n).extent :=
    trajectory.extent_tends_atTop (eventually_ge_atTop (M + 1))
  rcases Filter.Eventually.exists hev with ⟨n, hn⟩
  exact (Nat.not_succ_le_self M) (le_trans hn (hbounded n))

/-- Bounded physical linear extent cannot masquerade as simultaneous infinite-volume scaling. -/
theorem bounded_physical_extent_blocked
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (R : ℝ) (hbounded : ∀ n,
      latticePhysicalLinearExtent (trajectory.lattice n) (trajectory.spacing n) ≤ R) : False := by
  have hev : ∀ᶠ n in atTop, R + 1 ≤
      latticePhysicalLinearExtent (trajectory.lattice n) (trajectory.spacing n) :=
    trajectory.physical_extent_tends_atTop (eventually_ge_atTop (R + 1))
  rcases Filter.Eventually.exists hev with ⟨n, hn⟩
  linarith [hbounded n]

/-- A constant strictly positive bare coupling cannot satisfy the UV coupling condition. -/
theorem fixed_positive_bare_coupling_blocked
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    (g : ℝ) (hg : 0 < g)
    (hfixed : ∀ n, trajectory.bareGaugeCoupling n = g) : False := by
  have heq : trajectory.bareGaugeCoupling = fun _ : ℕ => g := funext hfixed
  have hconst : Tendsto trajectory.bareGaugeCoupling atTop (𝓝 g) := by
    rw [heq]
    exact tendsto_const_nhds
  have hzero : g = 0 := tendsto_nhds_unique hconst trajectory.bareGaugeCoupling_tends_zero
  linarith

/-- Injective normalization prevents equal action coefficients from hiding unequal bare couplings. -/
theorem action_coefficient_cannot_discard_bare_coupling
    (trajectory : FiniteLatticeScalingTrajectoryData d G)
    {m n : ℕ}
    (hcoefficient : (trajectory.actionCoupling m).coefficient =
      (trajectory.actionCoupling n).coefficient) :
    trajectory.bareGaugeCoupling m = trajectory.bareGaugeCoupling n := by
  apply trajectory.actionCoefficientFromBareCoupling_injective
  rw [← trajectory.actionCoefficient_coherence m,
    ← trajectory.actionCoefficient_coherence n]
  exact hcoefficient

variable
    {ContinuumObservable : Type*}
    {continuumExpectation : ContinuumObservable → ℂ}
    {trajectory : FiniteLatticeScalingTrajectoryData d G}

/-- The target unit and nontrivial observable cannot be the same constant-only label. -/
theorem constant_only_bridge_blocked
    (bridge : LatticeToContinuumObservableExpectationBridgeData trajectory
      ContinuumObservable continuumExpectation) :
    bridge.nontrivialObservable ≠ bridge.unitObservable := by
  intro heq
  obtain ⟨link, U, V, _, hne⟩ := bridge.nontrivial_lattice_dependence 0
  apply hne
  have hunit := bridge.latticeApproximation_unit 0
  rw [heq, hunit]

/-- The unit target normalization is tied to exact constant-one approximants at every cutoff. -/
theorem exact_unit_approximants
    (bridge : LatticeToContinuumObservableExpectationBridgeData trajectory
      ContinuumObservable continuumExpectation) (n : ℕ) :
    (bridge.latticeApproximation n bridge.unitObservable).observable.toFun =
      (fun _ => (1 : ℂ)) ∧
      continuumExpectation bridge.unitObservable = 1 :=
  ⟨bridge.latticeApproximation_unit n, bridge.continuumExpectation_unit⟩

/-- A different claimed target value cannot share the exact convergent expectation net. -/
theorem unrelated_continuum_limit_blocked
    (bridge : LatticeToContinuumObservableExpectationBridgeData trajectory
      ContinuumObservable continuumExpectation)
    (O : ContinuumObservable) (z : ℂ)
    (hz : Tendsto (fun n => scalingTrajectoryExpectation trajectory n
      (bridge.latticeApproximation n O)) atTop (𝓝 z)) :
    z = continuumExpectation O :=
  tendsto_nhds_unique hz (bridge.expectation_converges O)

/-- Every designated nontrivial approximant has actual one-link dependence. -/
theorem exact_nontrivial_approximant_dependence
    (bridge : LatticeToContinuumObservableExpectationBridgeData trajectory
      ContinuumObservable continuumExpectation) (n : ℕ) :
    ∃ link : PositiveOrientedLink d (trajectory.lattice n),
      DependsNontriviallyOnLink
        (bridge.latticeApproximation n bridge.nontrivialObservable) link :=
  bridge.nontrivial_lattice_dependence n

end YangMills.Lattice.LatticeScalingTrajectory.Probes
