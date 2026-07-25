/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubeGeometry
import YangMills.Minkowski.WightmanJointTemperedCorrelators
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Distributional boundary values of Wightman tube functions

Streater–Wightman printed p. 114, Theorem 3-5, states that the relative-coordinate tempered
correlator is the distributional boundary value of a holomorphic function on the backward tube.
This module packages the analytic and boundary-limit semantics without constructing a function.
Every admissible forward imaginary-direction tuple participates in the neighborhood filter; the
interface is not weakened to one selected ray.

The regularized boundary distributions are required to be actual integrals of the tube function
against Schwartz tests, with explicit integrability, preventing Mathlib's nonintegrable-zero
convention from satisfying the interface silently. Convergence uses Mathlib's pointwise/weak
continuous-linear-map topology on tempered distributions; no strong-dual claim is made. Polynomial growth and extended-tube continuation
remain separate obligations.
-/

namespace YangMills.Minkowski

open MeasureTheory
open scoped SchwartzMap

/-- Tuples of imaginary directions lying coordinatewise in the strict forward cone. -/
def wightmanForwardDirectionSet (d : EuclideanDimension) (n : ℕ) :
    Set (Fin n → Spacetime d) :=
  {η | ∀ j, η j ∈ openForwardMomentumCone d}

/-- The strict forward-direction set is open. -/
theorem isOpen_wightmanForwardDirectionSet
    (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanForwardDirectionSet d n) := by
  have hopen : ∀ j : Fin n, IsOpen
      {η : Fin n → Spacetime d | η j ∈ openForwardMomentumCone d} := by
    intro j
    exact (isOpen_openForwardMomentumCone d).preimage (continuous_apply j)
  have hinter := isOpen_iInter_of_finite hopen
  have hset : wightmanForwardDirectionSet d n = ⋂ j : Fin n,
      {η : Fin n → Spacetime d | η j ∈ openForwardMomentumCone d} := by
    ext η
    simp [wightmanForwardDirectionSet]
  rw [hset]
  exact hinter

/-- Standard tuple of future unit-time imaginary directions. -/
def standardWightmanForwardDirection
    (d : EuclideanDimension) (n : ℕ) : Fin n → Spacetime d :=
  fun _ => d.basisVector d.timeIndex

/-- Every positive rescaling of the standard direction remains strictly future-directed. -/
theorem positive_smul_standardWightmanForwardDirection_mem
    (d : EuclideanDimension) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    t • standardWightmanForwardDirection d n ∈
      wightmanForwardDirectionSet d n := by
  intro j
  constructor
  · simp [standardWightmanForwardDirection,
      EuclideanDimension.basisVector, EuclideanDimension.timeIndex, ht]
  · change 0 < d.minkowskiQuadraticForm
      (t • d.basisVector d.timeIndex)
    rw [QuadraticMap.map_smul, d.minkowskiQuadraticForm_time_basisVector]
    simpa using mul_pos ht ht

/-- Positive standard directions genuinely tend to zero, so the boundary filter is not isolated
from its strict source domain. -/
theorem standardWightmanForwardDirection_tendsto_zero
    (d : EuclideanDimension) (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => t • standardWightmanForwardDirection d n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hcontinuous : Continuous
      (fun t : ℝ => t • standardWightmanForwardDirection d n) := by
    fun_prop
  have htendsto : Filter.Tendsto
      (fun t : ℝ => t • standardWightmanForwardDirection d n)
      (nhds 0) (nhds ((0 : ℝ) • standardWightmanForwardDirection d n)) :=
    hcontinuous.continuousAt
  change Filter.Tendsto
    (fun t : ℝ => t • standardWightmanForwardDirection d n)
    (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) (nhds 0)
  have hle : nhds (0 : ℝ) ⊓ Filter.principal (Set.Ioi 0) ≤ nhds 0 :=
    inf_le_left
  simpa only [zero_smul] using htendsto.mono_left hle

/-- The all-direction boundary filter is nontrivial. At positive arity the witnessing standard ray
contains nonzero strict directions; at arity zero the direction carrier is the expected singleton. -/
theorem wightmanForwardDirection_nhdsWithin_neBot
    (d : EuclideanDimension) (n : ℕ) :
    (nhdsWithin 0 (wightmanForwardDirectionSet d n)).NeBot := by
  let source : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hzero := standardWightmanForwardDirection_tendsto_zero d n
  have hpositive : ∀ᶠ t : ℝ in source, 0 < t := by
    exact self_mem_nhdsWithin
  have hmem : ∀ᶠ t : ℝ in source,
      t • standardWightmanForwardDirection d n ∈
        wightmanForwardDirectionSet d n := by
    filter_upwards [hpositive] with t ht
    exact positive_smul_standardWightmanForwardDirection_mem d n ht
  have hprincipal : Filter.Tendsto
      (fun t : ℝ => t • standardWightmanForwardDirection d n) source
      (Filter.principal (wightmanForwardDirectionSet d n)) :=
    Filter.tendsto_principal.2 hmem
  have hwithin : Filter.Tendsto
      (fun t : ℝ => t • standardWightmanForwardDirection d n) source
      (nhdsWithin 0 (wightmanForwardDirectionSet d n)) := by
    exact Filter.tendsto_inf.2 ⟨hzero, hprincipal⟩
  haveI : source.NeBot := by
    dsimp [source]
    infer_instance
  exact hwithin.neBot

/-- At positive arity, every positive point on the standard ray is nonzero. -/
theorem positive_smul_standardWightmanForwardDirection_ne_zero
    (d : EuclideanDimension) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    t • standardWightmanForwardDirection d n ≠ 0 := by
  intro hzero
  let j : Fin n := ⟨0, hn⟩
  have atTime := congrArg (fun η : Fin n → Spacetime d => η j d.timeIndex) hzero
  simp [standardWightmanForwardDirection, EuclideanDimension.basisVector,
    EuclideanDimension.timeIndex, ne_of_gt ht] at atTime

/-- Real relative coordinates approached with imaginary part `-η`. -/
def wightmanTubeApproachPoint
    {d : EuclideanDimension} {n : ℕ}
    (ξ η : Mathematics.FiniteConfiguration (Spacetime d) n) :
    Fin n → ComplexifiedSpacetime d :=
  fun j i => Complex.ofReal (ξ j i) - Complex.I * Complex.ofReal (η j i)

/-- Every strict forward direction gives a point of the exact backward tube. -/
theorem wightmanTubeApproachPoint_mem
    {d : EuclideanDimension} {n : ℕ}
    {ξ η : Mathematics.FiniteConfiguration (Spacetime d) n}
    (hη : η ∈ wightmanForwardDirectionSet d n) :
    wightmanTubeApproachPoint ξ η ∈ wightmanBackwardTube d n := by
  intro j
  have himag :
      -complexifiedSpacetimeImaginaryPart (wightmanTubeApproachPoint ξ η j) = η j := by
    funext i
    simp [wightmanTubeApproachPoint, complexifiedSpacetimeImaginaryPart]
  rw [himag]
  exact hη j

/-- Holomorphic tube function with an exact tempered distributional boundary value.

`boundary` is supplied independently (for example, by relative-coordinate Wightman data), but all
approximants are forced to come from this exact `tubeFunction` by Lebesgue integration. -/
structure WightmanTubeBoundaryValueData
    (d : EuclideanDimension) (n : ℕ)
    (boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ) where
  /-- Candidate holomorphic function on the complexified relative-coordinate carrier. -/
  tubeFunction : (Fin n → ComplexifiedSpacetime d) → ℂ
  /-- Genuine holomorphy on the exact open backward tube. -/
  holomorphic : DifferentiableOn ℂ tubeFunction (wightmanBackwardTube d n)
  /-- Regularized distribution at every imaginary-direction tuple. -/
  boundaryApproximation :
    Mathematics.FiniteConfiguration (Spacetime d) n →
      TemperedDistribution (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ
  /-- Every source-facing regularized integral is genuinely integrable. -/
  approximation_integrable : ∀ η ∈ wightmanForwardDirectionSet d n,
    ∀ test : ScalarMinkowskiNPointSchwartzTestFunction d n,
      Integrable (fun ξ => tubeFunction (wightmanTubeApproachPoint ξ η) * test ξ)
  /-- Every regularized distribution is exactly integration of the same tube function. -/
  approximation_coherent : ∀ η ∈ wightmanForwardDirectionSet d n,
    ∀ test : ScalarMinkowskiNPointSchwartzTestFunction d n,
      boundaryApproximation η test =
        ∫ ξ, tubeFunction (wightmanTubeApproachPoint ξ η) * test ξ
  /-- Distributional convergence as all strict forward directions tend jointly to zero. -/
  boundary_tendsto : Filter.Tendsto boundaryApproximation
    (nhdsWithin 0 (wightmanForwardDirectionSet d n)) (nhds boundary)

end YangMills.Minkowski
