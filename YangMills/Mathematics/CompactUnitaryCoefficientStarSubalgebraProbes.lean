/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactUnitaryCoefficientStarSubalgebra

/-!
# Hostile probes for the compact unitary coefficient star subalgebra
-/

namespace YangMills
namespace Mathematics
namespace CompactUnitaryCoefficientStarSubalgebra
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The bundled continuous coefficient evaluates to the original matrix entry exactly. -/
theorem exact_continuous_coefficient_evaluation
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (i j : Fin n) (g : G) :
    continuousMatrixRepresentationCoefficient ρ hρ i j g = ρ g i j :=
  rfl

/-- One is directly in the generator set, independently of any trivial-representation
construction. -/
theorem exact_constant_one_generator :
    (1 : C(G, ℂ)) ∈ compactUnitaryCoefficientGenerators (G := G) :=
  Or.inl rfl

/-- Constants are explicit generators, so the generating span is not empty. -/
theorem exact_constant_one_membership :
    (1 : C(G, ℂ)) ∈ compactUnitaryCoefficientSpan (G := G) :=
  one_mem_compactUnitaryCoefficientSpan

/-- Every bundled irreducible-unitary coefficient enters through the advertised generator set. -/
theorem exact_irreducible_unitary_generator
    (ρ : ContinuousUnitaryIrreducibleMatrixRepresentation G)
    (i j : Fin ρ.dimension) :
    ρ.continuousCoefficient i j ∈ compactUnitaryCoefficientGenerators (G := G) :=
  Or.inr ⟨ρ, i, j, rfl⟩

variable [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Complete reducibility really places every continuous finite matrix coefficient in the span. -/
theorem exact_arbitrary_continuous_coefficient_membership
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (i j : Fin n) :
    continuousMatrixRepresentationCoefficient ρ hρ i j ∈
      compactUnitaryCoefficientSpan (G := G) :=
  continuousMatrixRepresentationCoefficient_mem_span ρ hρ i j

/-- Products of generating coefficients land in the same finite span. -/
theorem exact_generator_product_closure
    {f g : C(G, ℂ)}
    (hf : f ∈ compactUnitaryCoefficientGenerators (G := G))
    (hg : g ∈ compactUnitaryCoefficientGenerators (G := G)) :
    f * g ∈ compactUnitaryCoefficientSpan (G := G) :=
  compactUnitaryCoefficientGenerators_mul_mem_span hf hg

/-- Pointwise stars of generating coefficients land in the same finite span. -/
theorem exact_generator_star_closure
    {f : C(G, ℂ)} (hf : f ∈ compactUnitaryCoefficientGenerators (G := G)) :
    star f ∈ compactUnitaryCoefficientSpan (G := G) :=
  compactUnitaryCoefficientGenerators_star_mem_span hf

/-- The bundled star subalgebra is defined with exactly the finite-span carrier, rather than by
a closure or top construction. This does not assert that the span is extensionally proper. -/
theorem exact_starSubalgebra_carrier (f : C(G, ℂ)) :
    f ∈ compactUnitaryCoefficientStarSubalgebra (G := G) ↔
      f ∈ compactUnitaryCoefficientSpan (G := G) :=
  Iff.rfl

/-- Hostile carrier probe: replacing the exact finite span is contradictory. -/
theorem changed_starSubalgebra_carrier_blocked
    (changed : (compactUnitaryCoefficientStarSubalgebra (G := G) : Set C(G, ℂ)) ≠
      compactUnitaryCoefficientSpan (G := G)) : False :=
  changed rfl

/-- Multiplication closure is exposed by the bundled `StarSubalgebra`. -/
theorem exact_bundled_multiplication
    {f g : C(G, ℂ)}
    (hf : f ∈ compactUnitaryCoefficientStarSubalgebra (G := G))
    (hg : g ∈ compactUnitaryCoefficientStarSubalgebra (G := G)) :
    f * g ∈ compactUnitaryCoefficientStarSubalgebra (G := G) :=
  mul_mem hf hg

/-- Pointwise-star closure is exposed by the bundled `StarSubalgebra`. -/
theorem exact_bundled_star
    {f : C(G, ℂ)}
    (hf : f ∈ compactUnitaryCoefficientStarSubalgebra (G := G)) :
    star f ∈ compactUnitaryCoefficientStarSubalgebra (G := G) :=
  star_mem hf

/-- The bundle contains one without asserting point separation or density. -/
theorem bundled_one_mem :
    (1 : C(G, ℂ)) ∈ compactUnitaryCoefficientStarSubalgebra (G := G) :=
  one_mem _

/-- Every scalar constant enters through the algebra map. -/
theorem bundled_scalar_mem (c : ℂ) :
    algebraMap ℂ C(G, ℂ) c ∈ compactUnitaryCoefficientStarSubalgebra (G := G) :=
  (compactUnitaryCoefficientStarSubalgebra (G := G)).algebraMap_mem c

end

end Probes
end CompactUnitaryCoefficientStarSubalgebra
end Mathematics
end YangMills
