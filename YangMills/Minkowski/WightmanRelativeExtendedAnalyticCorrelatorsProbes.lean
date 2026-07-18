/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanRelativeExtendedAnalyticCorrelators

/-!
# Hostile probes for relative extended analytic correlators

The probes expose all-arity holomorphy and exact restriction to the same analytic boundary whose
tempered limit is the exact relative correlator distribution.
-/

namespace YangMills.Minkowski.WightmanRelativeExtendedAnalyticCorrelators.Probes

variable
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    {relative : ScalarWightmanRelativeAnalyticCorrelatorData full}

/-- Every arity extends exactly the ordinary tube datum indexed by the exact relative distribution. -/
theorem exact_all_arity_extended_boundary
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) :
    DifferentiableOn ℂ (data.extendedContinuation n).extendedFunction
        (wightmanExtendedTube d n) ∧
      ∀ z ∈ wightmanBackwardTube d n,
        (data.extendedContinuation n).extendedFunction z =
          (relative.analyticBoundary n).tubeFunction z :=
  ⟨(data.extendedContinuation n).holomorphic,
    (data.extendedContinuation n).restricts_to_ordinary⟩

/-- Every arity is invariant under the exact same proper complex Lorentz action. -/
theorem exact_all_arity_extended_invariance
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) (transformation : ProperComplexLorentzTransformation d)
    (z : Fin n → ComplexifiedSpacetime d) (hz : z ∈ wightmanExtendedTube d n) :
    (data.extendedContinuation n).extendedFunction
        (ProperComplexLorentzTransformation.actConfiguration transformation z) =
      (data.extendedContinuation n).extendedFunction z :=
  (data.extendedContinuation n).invariant transformation z hz

/-- Every represented orbit value is tied to the exact ordinary function whose boundary is the
same relative correlator distribution. -/
theorem exact_all_arity_orbit_source_value
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) (transformation : ProperComplexLorentzTransformation d)
    (source : Fin n → ComplexifiedSpacetime d)
    (source_mem : source ∈ wightmanBackwardTube d n) :
    (data.extendedContinuation n).extendedFunction
        (ProperComplexLorentzTransformation.actConfiguration transformation source) =
      (relative.analyticBoundary n).tubeFunction source :=
  (data.extendedContinuation n).value_eq_orbitSource
    transformation source source_mem

/-- The ordinary function under the extension still converges to the exact relative tempered
correlator distribution, not an unrelated boundary. -/
theorem exact_relative_boundary_retained
    (_data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) :
    Filter.Tendsto (relative.analyticBoundary n).boundaryApproximation
      (nhdsWithin 0 (wightmanForwardDirectionSet d n))
      (nhds (relative.relativeDistribution n)) :=
  (relative.analyticBoundary n).boundary_tendsto

/-- The explicit all-arity restriction theorem remains on the exact same relative chain. -/
theorem exact_relative_restriction
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) (z : Fin n → ComplexifiedSpacetime d)
    (hz : z ∈ wightmanBackwardTube d n) :
    (data.extendedContinuation n).extendedFunction z =
      (relative.analyticBoundary n).tubeFunction z :=
  data.restricts_to_relativeBoundary n z hz

/-- A continuation datum for an unrelated ordinary tube boundary has the wrong dependent type and
cannot replace the exact all-arity projection. This value-level probe exposes the resulting
mismatch whenever the ordinary functions differ. -/
theorem disconnected_relative_continuation_value_blocked
    (data : ScalarWightmanRelativeExtendedAnalyticCorrelatorData relative)
    (n : ℕ) (z : Fin n → ComplexifiedSpacetime d)
    (hz : z ∈ wightmanBackwardTube d n) (replacement : ℂ)
    (mismatch : replacement ≠ (relative.analyticBoundary n).tubeFunction z) :
    replacement ≠ (data.extendedContinuation n).extendedFunction z := by
  rw [data.restricts_to_relativeBoundary n z hz]
  exact mismatch

end YangMills.Minkowski.WightmanRelativeExtendedAnalyticCorrelators.Probes
