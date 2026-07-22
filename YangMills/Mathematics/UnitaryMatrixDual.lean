/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryFiniteCoefficientFamilyPlancherel

/-!
# The coordinate unitary dual of a topological group

This file bundles positive-dimensional continuous irreducible unitary complex matrix
representations and quotients them by exact representation equivalence. The quotient
`UnitaryMatrixDual G` is therefore an all-class indexing carrier for the coordinate representations
covered by this bundle.

A noncomputable representative is selected from each quotient class. The construction proves:

* every bundled representation is equivalent to its selected class representative;
* representatives of distinct quotient classes are inequivalent;
* an injectively labelled family of quotient classes supplies exactly the pairwise-inequivalence
  certificates required by finite Fourier/Plancherel blocks.

This is an algebraic quotient construction, not Peter–Weyl. It does not prove that arbitrary
abstract finite-dimensional representations can be put into these unitary coordinates, that the dual is
countable, or that its coefficient functions are dense or complete in `C(G)` or `L²(G)`.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

/-- A positive-dimensional continuous irreducible unitary representation in explicit finite matrix
coordinates. -/
structure ContinuousUnitaryIrreducibleMatrixRepresentation
 (G:Type uG) [Group G] [TopologicalSpace G] where
 dimension : ℕ
 dimension_pos : 0 < dimension
 representation : G →* Matrix (Fin dimension) (Fin dimension) ℂ
 continuous_representation : Continuous representation
 unitary_representation : ∀g, star (representation g)*representation g=1
 irreducible_representation : Representation.IsIrreducible
  (matrixRepresentation representation)

/-- Exact representation equivalence across possibly different coordinate dimensions. -/
def ContinuousUnitaryIrreducibleMatrixRepresentation.IsEquivalent
 {G:Type uG} [Group G] [TopologicalSpace G]
 (ρ σ:ContinuousUnitaryIrreducibleMatrixRepresentation G) : Prop :=
 Nonempty (Representation.Equiv (matrixRepresentation ρ.representation)
  (matrixRepresentation σ.representation))

theorem ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_refl
 {G:Type uG} [Group G] [TopologicalSpace G]
 (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G) : ρ.IsEquivalent ρ :=
 ⟨Representation.Equiv.refl _⟩

theorem ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm
 {G:Type uG} [Group G] [TopologicalSpace G]
 {ρ σ:ContinuousUnitaryIrreducibleMatrixRepresentation G} :
 ρ.IsEquivalent σ → σ.IsEquivalent ρ := by
 rintro ⟨e⟩
 exact ⟨e.symm⟩

theorem ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_trans
 {G:Type uG} [Group G] [TopologicalSpace G]
 {ρ σ τ:ContinuousUnitaryIrreducibleMatrixRepresentation G} :
 ρ.IsEquivalent σ → σ.IsEquivalent τ → ρ.IsEquivalent τ := by
 rintro ⟨e⟩ ⟨f⟩
 exact ⟨e.trans f⟩

/-- Equivalent coordinate representations have equal matrix dimensions. -/
theorem ContinuousUnitaryIrreducibleMatrixRepresentation.dimension_eq_of_isEquivalent
 {G : Type uG} [Group G] [TopologicalSpace G]
 {ρ σ : ContinuousUnitaryIrreducibleMatrixRepresentation G}
 (equivalent : ρ.IsEquivalent σ) : ρ.dimension = σ.dimension := by
 rcases equivalent with ⟨equivalence⟩
 have finrankEquality := equivalence.toLinearEquiv.finrank_eq
 simpa using finrankEquality

instance continuousUnitaryIrreducibleMatrixRepresentationSetoid
 (G:Type uG) [Group G] [TopologicalSpace G] :
 Setoid (ContinuousUnitaryIrreducibleMatrixRepresentation G) where
 r := ContinuousUnitaryIrreducibleMatrixRepresentation.IsEquivalent
 iseqv := ⟨
  ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_refl,
  @ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm G _ _,
  @ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_trans G _ _⟩

/-- The coordinate unitary dual: equivalence classes of bundled continuous irreducible unitary
matrix representations. -/
def UnitaryMatrixDual
 (G:Type uG) [Group G] [TopologicalSpace G] :=
 Quotient (continuousUnitaryIrreducibleMatrixRepresentationSetoid G)

def unitaryMatrixDualClass
 {G:Type uG} [Group G] [TopologicalSpace G]
 (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G) :
 UnitaryMatrixDual G := Quotient.mk _ ρ

/-- A noncomputably selected matrix representative of a unitary-dual class. -/
def unitaryMatrixDualRepresentative
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 ContinuousUnitaryIrreducibleMatrixRepresentation G := Quotient.out q

@[simp] theorem unitaryMatrixDualClass_representative
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 unitaryMatrixDualClass (unitaryMatrixDualRepresentative q) = q :=
 Quotient.out_eq q

/-- Two bundled representations define the same dual class exactly when they are equivalent. -/
theorem unitaryMatrixDualClass_eq_iff
 {G:Type uG} [Group G] [TopologicalSpace G]
 (ρ σ:ContinuousUnitaryIrreducibleMatrixRepresentation G) :
 unitaryMatrixDualClass ρ = unitaryMatrixDualClass σ ↔
   ρ.IsEquivalent σ := by
 exact Quotient.eq

/-- Every bundled representation is equivalent to the selected representative of its class. -/
theorem unitaryMatrixDual_equivalent_representative
 {G:Type uG} [Group G] [TopologicalSpace G]
 (ρ:ContinuousUnitaryIrreducibleMatrixRepresentation G) :
 ρ.IsEquivalent (unitaryMatrixDualRepresentative
   (unitaryMatrixDualClass ρ)) := by
 have h : (unitaryMatrixDualRepresentative
      (unitaryMatrixDualClass ρ)).IsEquivalent ρ :=
   @Quotient.mk_out _
     (continuousUnitaryIrreducibleMatrixRepresentationSetoid G) ρ
 exact ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm h

def unitaryMatrixDualDimension
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) : ℕ :=
 (unitaryMatrixDualRepresentative q).dimension

def unitaryMatrixDualRepresentation
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 G→*Matrix (Fin (unitaryMatrixDualDimension q))
  (Fin (unitaryMatrixDualDimension q)) ℂ :=
 (unitaryMatrixDualRepresentative q).representation

theorem unitaryMatrixDualDimension_pos
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) : 0<unitaryMatrixDualDimension q :=
 (unitaryMatrixDualRepresentative q).dimension_pos

theorem continuous_unitaryMatrixDualRepresentation
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 Continuous (unitaryMatrixDualRepresentation q) :=
 (unitaryMatrixDualRepresentative q).continuous_representation

theorem unitary_unitaryMatrixDualRepresentation
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) (g:G) :
 star (unitaryMatrixDualRepresentation q g)*
  unitaryMatrixDualRepresentation q g=1 :=
 (unitaryMatrixDualRepresentative q).unitary_representation g

noncomputable instance unitaryMatrixDualRepresentation_irreducible
 {G:Type uG} [Group G] [TopologicalSpace G]
 (q:UnitaryMatrixDual G) :
 Representation.IsIrreducible
  (matrixRepresentation (unitaryMatrixDualRepresentation q)) :=
 (unitaryMatrixDualRepresentative q).irreducible_representation

/-- Selected representatives of distinct quotient classes are genuinely inequivalent. -/
theorem unitaryMatrixDual_representative_inequivalent
 {G:Type uG} [Group G] [TopologicalSpace G]
 {q r:UnitaryMatrixDual G} (hqr:q≠r) :
 IsEmpty (Representation.Equiv
  (matrixRepresentation (unitaryMatrixDualRepresentation r))
  (matrixRepresentation (unitaryMatrixDualRepresentation q))) := by
 constructor
 intro e
 apply hqr
 have hclasses : unitaryMatrixDualClass
    (unitaryMatrixDualRepresentative r) =
   unitaryMatrixDualClass (unitaryMatrixDualRepresentative q) :=
  Quotient.sound ⟨e⟩
 calc
  q = unitaryMatrixDualClass (unitaryMatrixDualRepresentative q) :=
   (unitaryMatrixDualClass_representative q).symm
  _ = unitaryMatrixDualClass (unitaryMatrixDualRepresentative r) := hclasses.symm
  _ = r := unitaryMatrixDualClass_representative r

/-- Injective labels into the unitary dual produce pairwise-inequivalent representative
certificates with the orientation used by finite Fourier families. -/
theorem unitaryMatrixDual_pairwiseInequivalent
 {G:Type uG} [Group G] [TopologicalSpace G]
 {ι:Type*} (label:ι→UnitaryMatrixDual G)
 (hlabel:Function.Injective label) (i j:ι) (hij:i≠j) :
 IsEmpty (Representation.Equiv
  (matrixRepresentation (unitaryMatrixDualRepresentation (label j)))
  (matrixRepresentation (unitaryMatrixDualRepresentation (label i)))) := by
 apply unitaryMatrixDual_representative_inequivalent
 intro equality
 exact hij (hlabel equality)

end

end Mathematics
end YangMills
