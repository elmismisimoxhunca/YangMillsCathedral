/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.OrthonormalBilinearContraction

/-!
# Hostile probes for canonical orthonormal bilinear contraction
-/

namespace YangMills.Mathematics.Probes

open scoped BigOperators

universe uE uW uι uκ

noncomputable section

variable
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {W : Type uW} [AddCommGroup W] [Module ℝ W]
    {ι : Type uι} [Fintype ι]
    {κ : Type uκ} [Fintype κ]

/-- A double-sum presentation in an orthonormal basis cannot differ from the canonical tensor
contraction. -/
theorem orthonormal_sum_canonical_mismatch_blocked
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W)
    (basis : OrthonormalBasis ι ℝ E)
    (mismatch :
      canonicalBilinearQuadraticContraction pairing bilinear ≠
        ∑ i, ∑ j,
          pairing (bilinear (basis i) (basis j)) (bilinear (basis i) (basis j))) : False :=
  mismatch (canonicalBilinearQuadraticContraction_eq_sum pairing bilinear basis)

/-- Two orthonormal bases cannot produce different double-contraction sums. -/
theorem orthonormal_basis_dependence_blocked
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear : E →ₗ[ℝ] E →ₗ[ℝ] W)
    (first : OrthonormalBasis ι ℝ E)
    (second : OrthonormalBasis κ ℝ E)
    (mismatch :
      (∑ i, ∑ j,
        pairing (bilinear (first i) (first j)) (bilinear (first i) (first j))) ≠
      ∑ i, ∑ j,
        pairing (bilinear (second i) (second j)) (bilinear (second i) (second j))) : False :=
  mismatch
    (orthonormalBilinearQuadraticContraction_independent
      pairing bilinear first second)

/-- An unrelated bilinear map cannot replace the supplied map when it changes the canonical
contraction. -/
theorem unrelated_bilinearMap_substitution_blocked
    (pairing : W →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    (bilinear candidate : E →ₗ[ℝ] E →ₗ[ℝ] W)
    (changesContraction :
      canonicalBilinearQuadraticContraction pairing candidate ≠
        canonicalBilinearQuadraticContraction pairing bilinear)
    (claimsSubstitution :
      canonicalBilinearQuadraticContraction pairing bilinear =
        canonicalBilinearQuadraticContraction pairing candidate) : False :=
  changesContraction claimsSubstitution.symm

end

end YangMills.Mathematics.Probes
