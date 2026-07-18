/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WeakBilocalDiagonalProbe
import YangMills.Mathematics.BilocalDifferenceFirstAnchor
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Weak finite-order operator-product-expansion interface

Wilson 1969, §II, equation `(2.2)`, expands `A(x)B(y)` into local fields with singular coefficient
functions/distributions, weakly between fixed states as `y → x`. The source further states that the
full expansion can contain infinitely many local fields while only finitely many contribute at each
finite order.

This module packages those semantics without constructing an OPE. A reusable relative/first-anchor
contraction combines a coefficient tempered distribution with one exact local-field matrix element.
Each order has a finite monotone truncation, an exact full-product remainder, and a little-`o`
condition against every normalized compact-anchor diagonal probe. Coefficients are generic tempered
distributions; matching their singularities to asymptotic freedom/perturbative renormalization is a
separate, still-open Yang–Mills obligation.
-/

namespace YangMills.Minkowski

open Filter Topology
open Asymptotics
open YangMills.Mathematics

/-- Relative-coordinate carrier for one ordered bilocal difference `x₀ - x₁`. -/
abbrev BilocalRelativeConfiguration (d : EuclideanDimension) := Spacetime d

/-- Bilinear contraction of a relative coefficient distribution and an anchor-local distribution
into one full ordered bilocal tempered distribution.

The pure relative/first-anchor law fixes the coordinate meaning; nondegeneracy blocks a zero contraction. -/
structure TemperedRelativeAnchorContractionData (d : EuclideanDimension) where
  contract :
    TemperedDistribution (BilocalRelativeConfiguration d) ℂ →ₗ[ℂ]
      TemperedDistribution (Spacetime d) ℂ →ₗ[ℂ]
        TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ
  pure_relative_anchor_coherent : ∀ coefficient localDistribution relativeTest anchorTest,
    contract coefficient localDistribution
        (bilocalDifferenceFirstAnchorSchwartzLift (Spacetime d) relativeTest anchorTest) =
      coefficient relativeTest * localDistribution anchorTest
  contract_ne_zero : ∀ coefficient localDistribution,
    coefficient ≠ 0 → localDistribution ≠ 0 →
      contract coefficient localDistribution ≠ 0

/-- Weak all-orders finite-truncation OPE data for one exact local-observable family and bilocal
product family. -/
structure WeakOperatorProductExpansionData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    (products : WeakTemperedBilocalObservableProductData family) where
  /-- A designated normalized controlled probe makes the universal probe quantifier nonempty in
  every accepted OPE datum. -/
  referenceProbe : WeakBilocalDiagonalProbeData d
  /-- Exact relative/first-anchor distribution contraction shared by every OPE term. -/
  contraction : TemperedRelativeAnchorContractionData d
  /-- Relative singular coefficient distribution for each ordered input pair and output local field. -/
  coefficient : family.Label → family.Label → family.Label →
    TemperedDistribution (BilocalRelativeConfiguration d) ℂ
  /-- Only finitely many output fields contribute at each requested order. -/
  truncation : ℕ → Finset family.Label
  /-- Higher-order truncations retain every lower-order output label. -/
  truncation_mono : Monotone truncation
  /-- Every nonzero coefficient label eventually enters a finite truncation; permanently unused
  coefficient metadata is forbidden. -/
  coefficient_eventually_in_truncation : ∀ A B C,
    coefficient A B C ≠ 0 → ∃ N, C ∈ truncation N
  /-- Exact full-product remainder for every order and weak matrix element. -/
  remainder : ℕ → family.Label → family.Label → D.domain → D.domain →
    TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ
  /-- The remainder is definitionally connected by equality to the same bilocal product and finite
  coefficient/local-field sum. -/
  remainder_eq : ∀ N A B ψ φ,
    remainder N A B ψ φ = products.bilocalMatrixElement A B ψ φ -
      ∑ C ∈ truncation N,
        contraction.contract (coefficient A B C) (family.matrixElement C ψ φ)
  /-- Weak near-diagonal asymptotics at every finite order, against every normalized compact-anchor
  probe. -/
  remainder_isLittleO : ∀ N A B ψ φ (probe : WeakBilocalDiagonalProbeData d),
    IsLittleO (𝓝[>] (0 : ℝ))
      (fun r => remainder N A B ψ φ (probe.test r))
      (fun r : ℝ => r ^ N)
  /-- At least one zeroth-order coefficient/truncation term is genuine. -/
  nontrivial_coefficient_witness :
    ∃ (A B C : family.Label) (ψ φ : D.domain),
      C ∈ truncation 0 ∧ coefficient A B C ≠ 0 ∧
      family.matrixElement C ψ φ ≠ 0

/-- Every OPE term has exact pure relative/first-anchor factorization into its coefficient and the same
local-field matrix element. -/
theorem WeakOperatorProductExpansionData.term_pure_relative_anchor
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    {products : WeakTemperedBilocalObservableProductData family}
    (ope : WeakOperatorProductExpansionData products)
    (A B C : family.Label) (ψ φ : D.domain)
    (relativeTest : SchwartzMap (BilocalRelativeConfiguration d) ℂ)
    (anchorTest : ScalarMinkowskiSchwartzTestFunction d) :
    ope.contraction.contract (ope.coefficient A B C) (family.matrixElement C ψ φ)
        (bilocalDifferenceFirstAnchorSchwartzLift (Spacetime d) relativeTest anchorTest) =
      ope.coefficient A B C relativeTest * family.matrixElement C ψ φ anchorTest :=
  ope.contraction.pure_relative_anchor_coherent _ _ _ _

/-- Truncation order zero is nonempty in every accepted OPE. -/
theorem WeakOperatorProductExpansionData.truncation_zero_nonempty
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    {products : WeakTemperedBilocalObservableProductData family}
    (ope : WeakOperatorProductExpansionData products) :
    (ope.truncation 0).Nonempty := by
  rcases ope.nontrivial_coefficient_witness with ⟨A, B, C, ψ, φ, hC, _, _⟩
  exact ⟨C, hC⟩

/-- Every accepted OPE has an actual nonzero contracted zeroth-order term on exact vectors. -/
theorem WeakOperatorProductExpansionData.exists_nonzero_zerothOrderTerm
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    [DecidableEq family.Label]
    {products : WeakTemperedBilocalObservableProductData family}
    (ope : WeakOperatorProductExpansionData products) :
    ∃ (A B C : family.Label) (ψ φ : D.domain),
      C ∈ ope.truncation 0 ∧
      ope.contraction.contract (ope.coefficient A B C)
        (family.matrixElement C ψ φ) ≠ 0 := by
  rcases ope.nontrivial_coefficient_witness with
    ⟨A, B, C, ψ, φ, hmem, hcoefficient, hlocal⟩
  exact ⟨A, B, C, ψ, φ, hmem,
    ope.contraction.contract_ne_zero _ _ hcoefficient hlocal⟩

end YangMills.Minkowski
