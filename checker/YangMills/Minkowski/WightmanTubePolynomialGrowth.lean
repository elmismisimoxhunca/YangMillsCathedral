/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanTubeBoundaryValue

/-!
# Polynomial growth on Wightman tubes

Streater–Wightman printed p. 54, Theorem 2-6, bounds a tube-holomorphic Laplace transform by a
polynomial in its real variables uniformly while the imaginary direction ranges over a compact
subset of the open cone. Printed p. 114 invokes this condition for Wightman functions.

This module selects the explicit radial normal form `C * (1 + ‖ξ‖)^N`. This describes the same
finite-dimensional polynomial-growth class as the printed arbitrary polynomial `P_K`, but the two
comparison directions are not yet formalized. It is therefore recorded as an explicit project
normal form rather than identified definitionally with the source formulation.
-/

namespace YangMills.Minkowski

/-- Uniform radial polynomial growth on compact subsets of strict forward imaginary directions. -/
def IsPolynomiallyBoundedOnWightmanTube
    (d : EuclideanDimension) (n : ℕ)
    (F : (Fin n → ComplexifiedSpacetime d) → ℂ) : Prop :=
  ∀ K : Set (Mathematics.FiniteConfiguration (Spacetime d) n),
    IsCompact K → K ⊆ wightmanForwardDirectionSet d n →
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ ξ : Mathematics.FiniteConfiguration (Spacetime d) n,
      ∀ η ∈ K,
        ‖F (wightmanTubeApproachPoint ξ η)‖ ≤ C * (1 + ‖ξ‖) ^ N

/-- Tube boundary data carrying the selected radial polynomial-growth normal form. -/
structure PolynomiallyBoundedWightmanTubeBoundaryValueData
    (d : EuclideanDimension) (n : ℕ)
    (boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ)
    extends WightmanTubeBoundaryValueData d n boundary where
  /-- Uniform polynomial growth on every compact strict direction set. -/
  polynomially_bounded : IsPolynomiallyBoundedOnWightmanTube d n tubeFunction

/-- Every singleton strict direction receives an explicit radial polynomial bound. -/
theorem PolynomiallyBoundedWightmanTubeBoundaryValueData.singleton_direction_bound
    {d : EuclideanDimension} {n : ℕ}
    {boundary : TemperedDistribution
      (Mathematics.FiniteConfiguration (Spacetime d) n) ℂ}
    (data : PolynomiallyBoundedWightmanTubeBoundaryValueData d n boundary)
    (η : Mathematics.FiniteConfiguration (Spacetime d) n)
    (hη : η ∈ wightmanForwardDirectionSet d n) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ ξ : Mathematics.FiniteConfiguration (Spacetime d) n,
        ‖data.tubeFunction (wightmanTubeApproachPoint ξ η)‖ ≤
          C * (1 + ‖ξ‖) ^ N := by
  rcases data.polynomially_bounded {η} (isCompact_singleton)
    (by intro q hq; rw [Set.mem_singleton_iff.mp hq]; exact hη) with ⟨C, N, hC, hbound⟩
  exact ⟨C, N, hC, fun ξ => hbound ξ η (by simp)⟩

end YangMills.Minkowski
