/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField
import YangMills.Mathematics.FiniteConfigurationSchwartzTensor

/-!
# Tempered local-observable families and weak bilocal products

Clay/Jaffe–Witten §4 asks for local quantum fields corresponding to gauge-invariant curvature
polynomials, and Wilson 1969, §II, equation `(2.2)`, formulates operator products weakly between
fixed states. This module builds a prerequisite shared-domain interface: a family of local tempered
operator-valued distributions and an actual full two-point tempered distribution for every ordered
pair and every ordered domain-vector matrix element.

Pure-tensor coherence fixes the bilocal operator order exactly. The unit field is smearing by the
Lebesgue integral, and explicit normalized/nontrivial witnesses block empty labels, a zero unit, and
zero bilocal products. This module does not yet interpret labels as curvature polynomials, define OPE
coefficients/remainders, impose covariance/locality, or construct any field, theory, or mass gap.
-/

namespace YangMills.Minkowski

open MeasureTheory
open YangMills.Mathematics

/-- Lebesgue smearing coefficient of the pointwise unit local field. -/
noncomputable def minkowskiSchwartzIntegral
    {d : EuclideanDimension} (f : ScalarMinkowskiSchwartzTestFunction d) : ℂ :=
  ∫ x, f x

/-- A family of scalar local operator-valued tempered distributions on one exact common domain. -/
structure TemperedLocalObservableFamilyData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) where
  /-- Labels for local observable fields; no gauge interpretation is silently assumed. -/
  Label : Type*
  /-- Distinguished pointwise unit field. -/
  unitLabel : Label
  /-- Every label acts on the same exact common domain. -/
  operator : Label → ScalarMinkowskiSchwartzTestFunction d →ₗ[ℂ] Module.End ℂ D.domain
  /-- Tempered matrix elements for every label and ordered domain-vector pair. -/
  matrixElement : Label → D.domain → D.domain → TemperedDistribution (Spacetime d) ℂ
  /-- Matrix elements evaluate the same labeled operators. -/
  matrixElement_coherent : ∀ label ψ φ f,
    matrixElement label ψ φ f =
      @inner ℂ H _ ψ.val (operator label f φ).val
  /-- The unit field is exactly the identity operator smeared by Lebesgue integral. -/
  unit_operator : ∀ f,
    operator unitLabel f = minkowskiSchwartzIntegral f • LinearMap.id
  /-- A concrete normalized test prevents the unit field from vanishing by normalization accident. -/
  normalizedUnitTest : ScalarMinkowskiSchwartzTestFunction d
  normalizedUnitTest_integral : minkowskiSchwartzIntegral normalizedUnitTest = 1
  /-- A genuinely different local-field label. -/
  nontrivialLabel : Label
  nontrivialLabel_ne_unit : nontrivialLabel ≠ unitLabel
  /-- The different label acts nontrivially on the exact domain. -/
  nontrivial_operator_witness :
    ∃ (f : ScalarMinkowskiSchwartzTestFunction d) (φ : D.domain),
      operator nontrivialLabel f φ ≠ 0 ∧
      operator nontrivialLabel f φ ≠ operator unitLabel f φ

/-- Exact full-product weak bilocal distributions for an ordered local-observable family. -/
structure WeakTemperedBilocalObservableProductData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D) where
  /-- Full two-configuration tempered matrix element of the ordered product `A(x)B(y)`. -/
  bilocalMatrixElement : family.Label → family.Label → D.domain → D.domain →
    TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ
  /-- On every pure tensor, the full distribution is exactly the same ordered operator product. -/
  pureTensor_coherent : ∀ A B ψ φ f g,
    bilocalMatrixElement A B ψ φ
        (scalarSchwartzPureTensor (Spacetime d) 2 ![f, g]) =
      @inner ℂ H _ ψ.val (family.operator A f (family.operator B g φ)).val
  /-- At least one exact product matrix element is nonzero, blocking a zero distribution family. -/
  nontrivial_product_witness :
    ∃ (A B : family.Label) (ψ φ : D.domain)
      (f g : ScalarMinkowskiSchwartzTestFunction d),
      @inner ℂ H _ ψ.val (family.operator A f (family.operator B g φ)).val ≠ 0

/-- The normalized unit test acts as the exact identity on the common domain. -/
theorem TemperedLocalObservableFamilyData.unit_normalizedTest_apply
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D) (φ : D.domain) :
    family.operator family.unitLabel family.normalizedUnitTest φ = φ := by
  rw [family.unit_operator, family.normalizedUnitTest_integral]
  simp

/-- The bilocal distribution is nonzero at the witnessed exact ordered pure tensor. -/
theorem WeakTemperedBilocalObservableProductData.exists_nonzero_distribution
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (products : WeakTemperedBilocalObservableProductData family) :
    ∃ (A B : family.Label) (ψ φ : D.domain),
      products.bilocalMatrixElement A B ψ φ ≠ 0 := by
  rcases products.nontrivial_product_witness with ⟨A, B, ψ, φ, f, g, hnonzero⟩
  refine ⟨A, B, ψ, φ, ?_⟩
  intro hzero
  have happly := congrArg
    (fun T : TemperedDistribution (FiniteConfiguration (Spacetime d) 2) ℂ =>
      T (scalarSchwartzPureTensor (Spacetime d) 2 ![f, g])) hzero
  rw [products.pureTensor_coherent] at happly
  simp at happly
  exact hnonzero happly

end YangMills.Minkowski
