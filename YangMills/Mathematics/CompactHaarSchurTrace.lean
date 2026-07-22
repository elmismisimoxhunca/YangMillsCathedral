/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.CompactHaarSchurSelf

/-!
# Trace normalization of the irreducible compact Haar–Schur scalar

Conjugation preserves matrix trace, so the normalized-Haar average
`∫ρ(g⁻¹)Aρ(g)dμ_H` has trace `tr(A)`. Combining this with the previously proved scalar-identity
form computes

`n * compactHaarSchurScalar = tr(A)`.

For positive dimension this gives the exact factor `tr(A)/n`. This is the normalization needed for
the self-case of matrix-coefficient orthogonality. The orthogonality formula itself, which also
requires a unitary-coordinate identification of inverse entries, is not asserted here.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Normalized-Haar conjugation averaging preserves matrix trace exactly. -/
theorem compactHaarIntertwinerAverage_trace_self
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (compactHaarIntertwinerAverage ρ ρ A) = Matrix.trace A := by
  let μ := normalizedCompactHaarMeasure G
  letI : IsProbabilityMeasure μ := normalizedCompactHaarMeasure_isProbability G
  rw [Matrix.trace]
  change (∑ i, ∫ g, (ρ (g⁻¹) * A * ρ g) i i ∂μ) = _
  rw [← integral_finsetSum Finset.univ]
  · calc
      (∫ g, ∑ i, (ρ (g⁻¹) * A * ρ g) i i ∂μ) =
          ∫ _g : G, Matrix.trace A ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        change Matrix.trace (ρ (g⁻¹) * A * ρ g) = Matrix.trace A
        calc
          Matrix.trace (ρ (g⁻¹) * A * ρ g) =
              Matrix.trace ((A * ρ g) * ρ (g⁻¹)) := by
            rw [Matrix.mul_assoc]
            exact Matrix.trace_mul_comm (ρ (g⁻¹)) (A * ρ g)
          _ = Matrix.trace A := by
            rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel,
              map_one, Matrix.mul_one]
      _ = Matrix.trace A := by simp
  · intro i _
    exact integrable_compactHaarIntertwinerAverage_integrand
      ρ ρ hρ hρ A i i

/-- The irreducible self-average scalar satisfies the exact undivided dimension normalization. -/
theorem natCast_mul_compactHaarSchurScalar_eq_trace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)] :
    (n : ℂ) * compactHaarSchurScalar ρ hρ A = Matrix.trace A := by
  have traceEquality := congrArg Matrix.trace
    (compactHaarIntertwinerAverage_eq_schurScalar_smul_one ρ hρ A)
  rw [compactHaarIntertwinerAverage_trace_self ρ hρ A] at traceEquality
  simpa [Matrix.trace, mul_comm] using traceEquality.symm

/-- In positive dimension, the exact Schur scalar is `tr(A)/n`. -/
theorem compactHaarSchurScalar_eq_inv_natCast_mul_trace
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) ℂ)
    (hρ : Continuous ρ) (A : Matrix (Fin n) (Fin n) ℂ)
    [Representation.IsIrreducible (matrixRepresentation ρ)]
    (dimension_pos : 0 < n) :
    compactHaarSchurScalar ρ hρ A =
      (n : ℂ)⁻¹ * Matrix.trace A := by
  rw [inv_mul_eq_div]
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.ne_of_gt dimension_pos))).2
  rw [mul_comm]
  exact natCast_mul_compactHaarSchurScalar_eq_trace ρ hρ A

end

end Mathematics
end YangMills
