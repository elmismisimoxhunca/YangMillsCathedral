/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WeakOperatorProductExpansion

/-!
# Hostile probes for weak operator-product expansions

The probes expose exact coefficient/local-field first-anchor contraction, finite monotone truncations, connected
remainders, all-order normalized-probe asymptotics, and nonzero coefficients. No OPE datum is built.
-/

namespace YangMills.Minkowski.WeakOperatorProductExpansion.Probes

open Filter Topology Asymptotics
open YangMills.Mathematics

variable
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

/-- Relative/first-anchor contraction is fixed on exact pure coordinate tests. -/
theorem exact_coefficient_local_factorization
    (ope : WeakOperatorProductExpansionData products)
    (A B C : family.Label) (ψ φ : D.domain)
    (relativeTest : SchwartzMap (BilocalRelativeConfiguration d) ℂ)
    (anchorTest : ScalarMinkowskiSchwartzTestFunction d) :
    ope.contraction.contract (ope.coefficient A B C) (family.matrixElement C ψ φ)
        (bilocalDifferenceFirstAnchorSchwartzLift (Spacetime d) relativeTest anchorTest) =
      ope.coefficient A B C relativeTest * family.matrixElement C ψ φ anchorTest :=
  ope.term_pure_relative_anchor A B C ψ φ relativeTest anchorTest

/-- The contraction cannot silently annihilate two nonzero factors. -/
theorem zero_contraction_blocked
    (ope : WeakOperatorProductExpansionData products)
    (coefficient : TemperedDistribution (BilocalRelativeConfiguration d) ℂ)
    (localDistribution : TemperedDistribution (Spacetime d) ℂ)
    (hcoefficient : coefficient ≠ 0) (hlocal : localDistribution ≠ 0) :
    ope.contraction.contract coefficient localDistribution ≠ 0 :=
  ope.contraction.contract_ne_zero coefficient localDistribution hcoefficient hlocal

/-- Zeroth order cannot use an empty output-field truncation. -/
theorem empty_zero_truncation_blocked
    (ope : WeakOperatorProductExpansionData products) :
    (ope.truncation 0).Nonempty :=
  ope.truncation_zero_nonempty

/-- Every lower-order output label remains present at every higher order. -/
theorem exact_truncation_monotonicity
    (ope : WeakOperatorProductExpansionData products)
    {m n : ℕ} (hmn : m ≤ n) :
    ope.truncation m ⊆ ope.truncation n :=
  ope.truncation_mono hmn

/-- Nonzero coefficient metadata cannot remain permanently outside all truncations. -/
theorem unused_nonzero_coefficient_blocked
    (ope : WeakOperatorProductExpansionData products)
    (A B C : family.Label) (hcoefficient : ope.coefficient A B C ≠ 0) :
    ∃ N, C ∈ ope.truncation N :=
  ope.coefficient_eventually_in_truncation A B C hcoefficient

/-- The universal probe quantifier is inhabited inside every accepted OPE datum. -/
theorem empty_probe_class_blocked
    (ope : WeakOperatorProductExpansionData products) :
    Nonempty (WeakBilocalDiagonalProbeData d) :=
  ⟨ope.referenceProbe⟩

/-- At least one exact coefficient and its same-label local matrix element are both nonzero. -/
theorem zero_coefficient_or_local_term_blocked
    (ope : WeakOperatorProductExpansionData products) :
    ∃ (A B C : family.Label) (ψ φ : D.domain),
      C ∈ ope.truncation 0 ∧ ope.coefficient A B C ≠ 0 ∧
      family.matrixElement C ψ φ ≠ 0 :=
  ope.nontrivial_coefficient_witness

/-- Consequently an actual contracted zeroth-order OPE term is nonzero. -/
theorem zero_zeroth_order_term_blocked
    (ope : WeakOperatorProductExpansionData products) :
    ∃ (A B C : family.Label) (ψ φ : D.domain),
      C ∈ ope.truncation 0 ∧
      ope.contraction.contract (ope.coefficient A B C)
        (family.matrixElement C ψ φ) ≠ 0 :=
  ope.exists_nonzero_zerothOrderTerm

/-- The remainder is tied to the same product, coefficients, local fields, vectors and order. -/
theorem exact_connected_remainder
    (ope : WeakOperatorProductExpansionData products)
    (N : ℕ) (A B : family.Label) (ψ φ : D.domain) :
    ope.remainder N A B ψ φ = products.bilocalMatrixElement A B ψ φ -
      ∑ C ∈ ope.truncation N,
        ope.contraction.contract (ope.coefficient A B C) (family.matrixElement C ψ φ) :=
  ope.remainder_eq N A B ψ φ

/-- A candidate remainder unequal to the exact finite subtraction is unrelated. -/
theorem unrelated_remainder_blocked
    (ope : WeakOperatorProductExpansionData products)
    (N : ℕ) (A B : family.Label) (ψ φ : D.domain)
    (candidate : TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ)
    (hcandidate : candidate ≠ products.bilocalMatrixElement A B ψ φ -
      ∑ C ∈ ope.truncation N,
        ope.contraction.contract (ope.coefficient A B C) (family.matrixElement C ψ φ)) :
    candidate ≠ ope.remainder N A B ψ φ := by
  intro heq
  apply hcandidate
  rw [heq, ope.remainder_eq]

/-- Every requested finite order is little-`o` against every normalized compact-anchor probe. -/
theorem exact_all_order_weak_asymptotics
    (ope : WeakOperatorProductExpansionData products)
    (N : ℕ) (A B : family.Label) (ψ φ : D.domain)
    (probe : WeakBilocalDiagonalProbeData d) :
    IsLittleO (𝓝[>] (0 : ℝ))
      (fun r => ope.remainder N A B ψ φ (probe.test r))
      (fun r : ℝ => r ^ N) :=
  ope.remainder_isLittleO N A B ψ φ probe

end YangMills.Minkowski.WeakOperatorProductExpansion.Probes
