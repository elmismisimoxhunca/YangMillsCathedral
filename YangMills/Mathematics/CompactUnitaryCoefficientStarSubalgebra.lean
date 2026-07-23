/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.FiniteRepresentationContragredient
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The finite irreducible-unitary coefficient star subalgebra

This file packages the finite complex span of continuous irreducible unitary matrix coefficients,
with constants explicitly adjoined, as a `StarSubalgebra ℂ C(G, ℂ)` for a compact Hausdorff group.

Multiplication closure is proved by identifying a product with one coefficient of the explicit
Kronecker tensor representation and then applying finite complete reducibility and Haar
unitarization. Pointwise star closure is proved by identifying a unitary coefficient's star with a
coefficient of its continuous contragredient and applying the same finite decomposition.

The construction does not assert that this star subalgebra separates points or is dense. Those are
separate Stone–Weierstrass/Peter–Weyl obligations.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A continuous matrix coefficient, bundled as a continuous map. -/
noncomputable def continuousMatrixRepresentationCoefficient {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) (i j : Fin n) : C(G, ℂ) :=
  ⟨fun g => ρ g i j, by fun_prop⟩

/-- A coefficient of a bundled continuous irreducible unitary representation. -/
noncomputable def ContinuousUnitaryIrreducibleMatrixRepresentation.continuousCoefficient
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (i j : Fin ρ.dimension) : C(G, ℂ) :=
  continuousMatrixRepresentationCoefficient ρ.representation ρ.continuous_representation i j

/-- Constants and all coefficients of positive-dimensional continuous irreducible unitary
matrix representations. Constants are adjoined explicitly rather than hidden behind a trivial
representation construction. -/
def compactUnitaryCoefficientGenerators : Set C(G, ℂ) :=
  {f | f = 1 ∨ ∃ (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (i j : Fin ρ.dimension), f = ρ.continuousCoefficient i j}

/-- The finite complex-linear span of the irreducible-unitary coefficient generators and constants. -/
def compactUnitaryCoefficientSpan : Submodule ℂ C(G, ℂ) :=
  Submodule.span ℂ (compactUnitaryCoefficientGenerators (G := G))

/-- The constant function one belongs to the coefficient span. -/
theorem one_mem_compactUnitaryCoefficientSpan :
    (1 : C(G, ℂ)) ∈ compactUnitaryCoefficientSpan (G := G) :=
  Submodule.subset_span (Or.inl rfl)

/-- Every bundled irreducible-unitary coefficient belongs to the generating span. -/
theorem continuousUnitaryCoefficient_mem_span
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (i j : Fin ρ.dimension) :
    ρ.continuousCoefficient i j ∈ compactUnitaryCoefficientSpan (G := G) :=
  Submodule.subset_span (Or.inr ⟨ρ,i,j,rfl⟩)

/-- Bundle one selected summand's positive dimension, continuity, unitarity, and
irreducibility data. -/
noncomputable def CompactRepresentationSelectedUnitaryDecomposition.unitaryData
    {n:ℕ} {ρ:G →* Matrix (Fin n) (Fin n) ℂ}
    (D:CompactRepresentationSelectedUnitaryDecomposition n ρ) (index:Fin D.count) :
    ContinuousUnitaryIrreducibleMatrixRepresentation G where
  dimension := D.dimension index
  dimension_pos := D.dimension_pos index
  representation := D.representation index
  continuous_representation := D.continuous_representation index
  unitary_representation := D.unitary_representation index
  irreducible_representation := D.irreducible_representation index

/-- Exact coefficient expansion for any supplied selected unitary decomposition, without
repeating the classical selection expression. -/
theorem CompactRepresentationSelectedUnitaryDecomposition.coefficient_expansion
    {n:ℕ} {ρ:G →* Matrix (Fin n) (Fin n) ℂ}
    (D:CompactRepresentationSelectedUnitaryDecomposition n ρ)
    (g:G) (row column:Fin n) :
    ρ g row column = ∑ index, ∑ sr, ∑ sc,
      finiteRepresentationDecompositionOutputCoordinate ρ D.summands D.decomposition index row
        (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)
          ((D.equivalence index).symm (Pi.single sr 1))) *
      D.representation index g sr sc *
      D.equivalence index
        ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)).symm
          (finiteRepresentationDecompositionInput ρ D.summands D.decomposition
            (Pi.single column 1) index)) sc :=
  finiteRepresentationDecomposition_reconstruct_coefficient_in_matrixSummands
    ρ D.summands D.decomposition D.dimension D.representation D.equivalence g row column

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Every coefficient of every continuous finite matrix representation of a compact group belongs
to the finite irreducible-unitary coefficient span. -/
theorem continuousMatrixRepresentationCoefficient_mem_span {n : ℕ}
    (ρ:G →* Matrix (Fin n) (Fin n) ℂ) (hρ:Continuous ρ) (row column:Fin n) :
    continuousMatrixRepresentationCoefficient ρ hρ row column ∈ compactUnitaryCoefficientSpan (G:=G) := by
  let D := compactRepresentationSelectedUnitaryDecomposition ρ hρ
  let term : ∀ index : Fin D.count, ∀ sr sc : Fin (D.dimension index), C(G,ℂ) :=
    fun index sr sc =>
      (finiteRepresentationDecompositionOutputCoordinate ρ D.summands D.decomposition index row
          (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)
            ((D.equivalence index).symm (Pi.single sr 1))) *
        D.equivalence index
          ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)).symm
            (finiteRepresentationDecompositionInput ρ D.summands D.decomposition
              (Pi.single column 1) index)) sc) •
      (D.unitaryData index).continuousCoefficient sr sc
  have equality : continuousMatrixRepresentationCoefficient ρ hρ row column =
      ∑ index, ∑ sr, ∑ sc, term index sr sc := by
    ext g
    change ρ g row column =
      (ContinuousMap.evalAlgHom ℂ ℂ g) (∑ index, ∑ sr, ∑ sc, term index sr sc)
    rw [D.coefficient_expansion g row column]
    rw [map_sum (ContinuousMap.evalAlgHom ℂ ℂ g)]
    simp_rw [map_sum (ContinuousMap.evalAlgHom ℂ ℂ g)]
    change (∑ index, ∑ sr, ∑ sc,
      finiteRepresentationDecompositionOutputCoordinate ρ D.summands D.decomposition index row
          (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)
            ((D.equivalence index).symm (Pi.single sr 1))) *
        D.representation index g sr sc *
        D.equivalence index
          ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)).symm
            (finiteRepresentationDecompositionInput ρ D.summands D.decomposition
              (Pi.single column 1) index)) sc) =
      ∑ index, ∑ sr, ∑ sc, term index sr sc g
    apply Finset.sum_congr rfl
    intro index _
    apply Finset.sum_congr rfl
    intro sr _
    apply Finset.sum_congr rfl
    intro sc _
    let a := finiteRepresentationDecompositionOutputCoordinate ρ D.summands D.decomposition
      index row (restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)
        ((D.equivalence index).symm (Pi.single sr 1)))
    let b := D.equivalence index
      ((restrictedGroupAlgebraSubmoduleLinearEquiv ρ (D.summands index)).symm
        (finiteRepresentationDecompositionInput ρ D.summands D.decomposition
          (Pi.single column 1) index)) sc
    change a * D.representation index g sr sc * b =
      (a * b) * D.representation index g sr sc
    ring
  rw [equality]
  apply Submodule.sum_mem
  intro index _
  apply Submodule.sum_mem
  intro sr _
  apply Submodule.sum_mem
  intro sc _
  exact Submodule.smul_mem _ _ (continuousUnitaryCoefficient_mem_span (D.unitaryData index) sr sc)

/-- The pointwise product of two generators belongs to the coefficient span. The
coefficient–coefficient case is one coefficient of the concrete Kronecker tensor representation. -/
theorem compactUnitaryCoefficientGenerators_mul_mem_span
    {f g:C(G,ℂ)} (hf:f ∈ compactUnitaryCoefficientGenerators (G:=G)) (hg:g ∈ compactUnitaryCoefficientGenerators (G:=G)) :
    f*g ∈ compactUnitaryCoefficientSpan (G:=G) := by
  rcases hf with rfl | ⟨ρ,i,j,rfl⟩
  · simpa [compactUnitaryCoefficientSpan] using (Submodule.subset_span hg)
  rcases hg with rfl | ⟨σ,k,l,rfl⟩
  · simpa using continuousUnitaryCoefficient_mem_span ρ i j
  let tensorCoefficient := continuousMatrixRepresentationCoefficient
    (matrixRepresentationTensorProduct ρ.representation σ.representation)
    (continuous_matrixRepresentationTensorProduct ρ.representation
      ρ.continuous_representation σ.representation σ.continuous_representation)
    (finProdEquivFinMul ρ.dimension σ.dimension (i,k))
    (finProdEquivFinMul ρ.dimension σ.dimension (j,l))
  have product_eq : ρ.continuousCoefficient i j * σ.continuousCoefficient k l =
      tensorCoefficient := by
    ext x
    change ρ.representation x i j * σ.representation x k l = _
    exact (matrixRepresentationTensorProduct_apply
      ρ.representation σ.representation x i j k l).symm
  rw [product_eq]
  exact continuousMatrixRepresentationCoefficient_mem_span _ _ _ _

/-- The pointwise star of a generator belongs to the coefficient span. The coefficient case is
a coefficient of the continuous contragredient representation. -/
theorem compactUnitaryCoefficientGenerators_star_mem_span
    {f:C(G,ℂ)} (hf:f ∈ compactUnitaryCoefficientGenerators (G:=G)) : star f ∈ compactUnitaryCoefficientSpan (G:=G) := by
  rcases hf with rfl | ⟨ρ,i,j,rfl⟩
  · simpa using one_mem_compactUnitaryCoefficientSpan (G:=G)
  let contraCoefficient := continuousMatrixRepresentationCoefficient
    (matrixRepresentationContragredient ρ.representation)
    (continuous_matrixRepresentationContragredient ρ.representation
      ρ.continuous_representation) i j
  have star_eq : star (ρ.continuousCoefficient i j) = contraCoefficient := by
    ext x
    exact (matrixRepresentationContragredient_apply_eq_star
      ρ.representation ρ.unitary_representation x i j).symm
  rw [star_eq]
  exact continuousMatrixRepresentationCoefficient_mem_span _ _ _ _

/-- The full finite coefficient span is closed under pointwise multiplication. -/
theorem compactUnitaryCoefficientSpan_mul_mem {f g : C(G, ℂ)}
    (hf:f ∈ compactUnitaryCoefficientSpan (G:=G)) (hg:g ∈ compactUnitaryCoefficientSpan (G:=G)) :
    f*g ∈ compactUnitaryCoefficientSpan (G:=G) := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ compactUnitaryCoefficientSpan (G:=G))
    ?_ ?_ ?_ ?_ hf
  · intro f hf
    refine Submodule.span_induction (p := fun g _ => f * g ∈ compactUnitaryCoefficientSpan (G:=G))
      ?_ ?_ ?_ ?_ hg
    · intro g hg
      exact compactUnitaryCoefficientGenerators_mul_mem_span hf hg
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add] using (Submodule.add_mem (compactUnitaryCoefficientSpan (G:=G)) hx hy)
    · intro a x _ hx
      have h := Submodule.smul_mem (compactUnitaryCoefficientSpan (G:=G)) a hx
      simpa [mul_smul_comm] using h
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using (Submodule.add_mem (compactUnitaryCoefficientSpan (G:=G)) hx hy)
  · intro a x _ hx
    have h := Submodule.smul_mem (compactUnitaryCoefficientSpan (G:=G)) a hx
    simpa [smul_mul_assoc] using h

/-- The full finite coefficient span is closed under pointwise star. -/
theorem compactUnitaryCoefficientSpan_star_mem {f : C(G, ℂ)}
    (hf : f ∈ compactUnitaryCoefficientSpan (G := G)) :
    star f ∈ compactUnitaryCoefficientSpan (G:=G) := by
  refine Submodule.span_induction (p := fun f _ => star f ∈ compactUnitaryCoefficientSpan (G:=G))
    ?_ ?_ ?_ ?_ hf
  · intro f hf
    exact compactUnitaryCoefficientGenerators_star_mem_span hf
  · simp
  · intro x y _ _ hx hy
    simpa using (Submodule.add_mem (compactUnitaryCoefficientSpan (G:=G)) hx hy)
  · intro a x _ hx
    have h := Submodule.smul_mem (compactUnitaryCoefficientSpan (G:=G)) (star a) hx
    simpa using h

/-- The finite span of constants and continuous irreducible-unitary coefficients, bundled as
an exact star subalgebra of complex-valued continuous functions on the compact group. -/
noncomputable def compactUnitaryCoefficientStarSubalgebra : StarSubalgebra ℂ C(G, ℂ) :=
  StarSubalgebra.mk
    { carrier := compactUnitaryCoefficientSpan (G:=G)
      mul_mem' := fun ha hb => compactUnitaryCoefficientSpan_mul_mem ha hb
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      algebraMap_mem' := by
        intro c
        have := Submodule.smul_mem (compactUnitaryCoefficientSpan (G:=G)) c (one_mem_compactUnitaryCoefficientSpan (G:=G))
        simpa [Algebra.smul_def] using this }
    (fun hf => compactUnitaryCoefficientSpan_star_mem hf)

end

end Mathematics
end YangMills
