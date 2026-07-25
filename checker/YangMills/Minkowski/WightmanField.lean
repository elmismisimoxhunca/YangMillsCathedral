/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.CommonInvariantDomain
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Scalar Wightman field and adjoint on one common domain

Streater–Wightman, printed p. 98, axiom `I`, requires smeared fields and their adjoints to preserve
one shared dense invariant domain and requires all domain-vector matrix elements to be tempered
distributions. This module packages one scalar field and its adjoint as operator-valued linear maps
on the exact previously selected common domain.

The field and adjoint matrix-element tempered distributions are explicitly connected to those same
operators. The adjoint relation uses the conjugated Schwartz test, matching
`Φ*(f) = Φ(conj f)*` with Mathlib's convention that the inner product is linear in its second slot.
A concrete nonzero Minkowski Schwartz bump prevents a vacuous test carrier.

No covariance, locality, cyclicity, field inhabitant, Wightman theory, spectrum, reconstruction,
existence theorem, or mass gap is introduced here.
-/

namespace YangMills.Minkowski

/-- Complex scalar Schwartz tests on the independent Minkowski coordinate carrier. -/
abbrev ScalarMinkowskiSchwartzTestFunction (d : EuclideanDimension) :=
  SchwartzMap (Spacetime d) ℂ

/-- Pointwise conjugation as a continuous real-linear operation on Minkowski Schwartz tests. -/
noncomputable def conjugateScalarMinkowskiSchwartzTestFunction
    {d : EuclideanDimension} :
    ScalarMinkowskiSchwartzTestFunction d →L[ℝ]
      ScalarMinkowskiSchwartzTestFunction d :=
  SchwartzMap.postcompCLM Complex.conjCLE

@[simp] theorem conjugateScalarMinkowskiSchwartzTestFunction_apply
    {d : EuclideanDimension} (f : ScalarMinkowskiSchwartzTestFunction d)
    (x : Spacetime d) :
    conjugateScalarMinkowskiSchwartzTestFunction f x = star (f x) :=
  rfl

/-- Conjugating a Minkowski Schwartz test twice restores it. -/
theorem conjugateScalarMinkowskiSchwartzTestFunction_involutive
    {d : EuclideanDimension} (f : ScalarMinkowskiSchwartzTestFunction d) :
    conjugateScalarMinkowskiSchwartzTestFunction
      (conjugateScalarMinkowskiSchwartzTestFunction f) = f := by
  ext x
  simp

/-- A compactly supported nonzero scalar Minkowski Schwartz test centered at the origin. -/
noncomputable def scalarMinkowskiSchwartzBump
    (d : EuclideanDimension) : ScalarMinkowskiSchwartzTestFunction d := by
  let bump : ContDiffBump (0 : Spacetime d) := {
    rIn := 1 / 4
    rOut := 1 / 2
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
  let complexBump : Spacetime d → ℂ := Complex.ofRealCLM ∘ bump
  have compact : HasCompactSupport complexBump := bump.hasCompactSupport.comp_left rfl
  have smooth : ContDiff ℝ (⊤ : ℕ∞) complexBump :=
    Complex.ofRealCLM.contDiff.comp bump.contDiff
  exact compact.toSchwartzMap smooth

/-- The explicit Minkowski Schwartz bump takes value one at the origin. -/
@[simp] theorem scalarMinkowskiSchwartzBump_zero
    (d : EuclideanDimension) : scalarMinkowskiSchwartzBump d 0 = 1 := by
  unfold scalarMinkowskiSchwartzBump
  change Complex.ofRealCLM (_ : ℝ) = 1
  rw [ContDiffBump.one_of_mem_closedBall]
  · norm_num
  · exact Metric.mem_closedBall_self (by norm_num)

/-- The explicit Minkowski Schwartz bump is genuinely nonzero. -/
theorem scalarMinkowskiSchwartzBump_ne_zero
    (d : EuclideanDimension) : scalarMinkowskiSchwartzBump d ≠ 0 := by
  intro hzero
  have atZero := congrArg
    (fun f : ScalarMinkowskiSchwartzTestFunction d => f 0) hzero
  rw [scalarMinkowskiSchwartzBump_zero] at atZero
  simp at atZero

/-- One scalar Wightman field and its adjoint preserving the exact common invariant domain, with
all matrix elements represented by tempered distributions. -/
structure ScalarWightmanFieldOnCommonDomainData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    (D : CommonInvariantDomainData vacuumData) where
  /-- The smeared field as an endomorphism of the exact common domain. -/
  field : ScalarMinkowskiSchwartzTestFunction d →ₗ[ℂ] Module.End ℂ D.domain
  /-- The smeared adjoint field on that same domain. -/
  adjointField : ScalarMinkowskiSchwartzTestFunction d →ₗ[ℂ] Module.End ℂ D.domain
  /-- Tempered matrix element of the field for every ordered domain-vector pair. -/
  matrixElement : D.domain → D.domain → TemperedDistribution (Spacetime d) ℂ
  /-- Matrix-element distributions evaluate the exact same field operator. -/
  matrixElement_coherent : ∀ ψ φ f,
    matrixElement ψ φ f = @inner ℂ H _ ψ.val (field f φ).val
  /-- Tempered matrix element of the adjoint field for every ordered domain-vector pair. -/
  adjointMatrixElement : D.domain → D.domain → TemperedDistribution (Spacetime d) ℂ
  /-- Adjoint matrix-element distributions evaluate the exact same adjoint operator. -/
  adjointMatrixElement_coherent : ∀ ψ φ f,
    adjointMatrixElement ψ φ f = @inner ℂ H _ ψ.val (adjointField f φ).val
  /-- Exact adjoint relation on the common domain and conjugated Schwartz test. -/
  adjoint_relation : ∀ ψ φ f,
    @inner ℂ H _ ψ.val (adjointField f φ).val =
      @inner ℂ H _ (field (conjugateScalarMinkowskiSchwartzTestFunction f) ψ).val φ.val

end YangMills.Minkowski
