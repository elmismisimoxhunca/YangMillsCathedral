/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import YangMills.Mathematics.UnitaryMatrixDualCentralContinuousFunctions

/-!
# Uniformly summable selected-character series

A unitary matrix has every entry bounded by one, so the trace character of a selected irreducible
representation satisfies

`‖χ_q(g)‖ ≤ dim(q)`

with equality in the global uniform norm because `χ_q(1) = dim(q)`. This file uses that sharp bound
to prove a character-series Weierstrass test: if

`∑ q, ‖a_q‖ dim(q)`

is summable, then `∑ q, a_q χ_q` converges unconditionally in `C(G, ℂ)`. The resulting continuous
function is central, its pointwise values are the corresponding unconditional scalar `tsum`, and its
uniform norm is bounded by the weighted scalar `tsum`.

This supplies exact convergence semantics needed by later heat-kernel work. No Casimir eigenvalue,
heat kernel, dual countability, or Peter–Weyl completeness is assumed.
-/

namespace YangMills
namespace Mathematics

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- One selected irreducible character as a continuous function. -/
noncomputable def unitaryMatrixDualContinuousCharacter
    (q : UnitaryMatrixDual G) : C(G, ℂ) :=
  ⟨unitaryMatrixDualCharacter q, continuous_unitaryMatrixDualCharacter q⟩

/-- Every selected representation value is a unitary matrix in Mathlib's exact matrix unitary
group. -/
theorem unitaryMatrixDualRepresentation_mem_unitaryGroup
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualRepresentation q g ∈
      Matrix.unitaryGroup (Fin (unitaryMatrixDualDimension q)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact (unitaryMatrixDualRepresentative q).unitary_representation g

/-- Sharp pointwise dimension bound for every selected irreducible character. -/
theorem norm_unitaryMatrixDualCharacter_le_dimension
    (q : UnitaryMatrixDual G) (g : G) :
    ‖unitaryMatrixDualCharacter q g‖ ≤ (unitaryMatrixDualDimension q : ℝ) := by
  unfold unitaryMatrixDualCharacter Matrix.trace
  calc
    ‖∑ i, unitaryMatrixDualRepresentation q g i i‖ ≤
        ∑ i, ‖unitaryMatrixDualRepresentation q g i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (unitaryMatrixDualDimension q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact entry_norm_bound_of_unitary
        (unitaryMatrixDualRepresentation_mem_unitaryGroup q g) i i
    _ = (unitaryMatrixDualDimension q : ℝ) := by simp

/-- The selected character takes the exact dimension value at the identity. -/
@[simp]
theorem unitaryMatrixDualCharacter_one
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCharacter q (1 : G) = (unitaryMatrixDualDimension q : ℂ) := by
  unfold unitaryMatrixDualCharacter
  rw [map_one]
  simp [Matrix.trace]

variable [CompactSpace G]

/-- The global uniform norm of a selected irreducible character is exactly its dimension. -/
theorem norm_unitaryMatrixDualContinuousCharacter
    (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualContinuousCharacter q‖ = (unitaryMatrixDualDimension q : ℝ) := by
  apply le_antisymm
  · rw [ContinuousMap.norm_le]
    · exact norm_unitaryMatrixDualCharacter_le_dimension q
    · positivity
  · calc
      (unitaryMatrixDualDimension q : ℝ) = ‖unitaryMatrixDualCharacter q (1 : G)‖ := by
        rw [unitaryMatrixDualCharacter_one]
        simp
      _ ≤ ‖unitaryMatrixDualContinuousCharacter q‖ :=
        ContinuousMap.norm_coe_le_norm (unitaryMatrixDualContinuousCharacter q) (1 : G)

/-- Evaluation at one point as a norm-nonincreasing continuous linear functional on `C(G, ℂ)`. -/
noncomputable def compactContinuousMapEvaluation
    (g : G) : C(G, ℂ) →L[ℂ] ℂ :=
  ({
    toFun := fun f : C(G, ℂ) => f g
    map_add' := by intro f h; rfl
    map_smul' := by intro c f; rfl
  } : C(G, ℂ) →ₗ[ℂ] ℂ).mkContinuous 1 (by
    intro f
    simpa using ContinuousMap.norm_coe_le_norm f g)

omit [Group G] in
@[simp]
theorem compactContinuousMapEvaluation_apply
    (g : G) (f : C(G, ℂ)) :
    compactContinuousMapEvaluation g f = f g :=
  rfl

/-- Weighted dimension summability implies unconditional uniform summability of the selected
character series. -/
theorem summable_unitaryMatrixDualContinuousCharacter_smul
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Summable (fun q => a q • unitaryMatrixDualContinuousCharacter q) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_unitaryMatrixDualContinuousCharacter] using h

/-- Unconditional selected-character sum in the global uniform norm. If the weighted summability
premise fails, Mathlib's `tsum` convention applies; every theorem below retains the premise. -/
noncomputable def unitaryMatrixDualUniformCharacterSeries
    (a : UnitaryMatrixDual G → ℂ) : C(G, ℂ) :=
  ∑' q, a q • unitaryMatrixDualContinuousCharacter q

/-- Exact unconditional `HasSum` statement in `C(G, ℂ)`. -/
theorem hasSum_unitaryMatrixDualUniformCharacterSeries
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    HasSum (fun q => a q • unitaryMatrixDualContinuousCharacter q)
      (unitaryMatrixDualUniformCharacterSeries a) :=
  (summable_unitaryMatrixDualContinuousCharacter_smul a h).hasSum

/-- The net of all finite selected-character sums converges in the global uniform norm. -/
theorem tendsto_finsetSum_unitaryMatrixDualContinuousCharacter
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, a q • unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualUniformCharacterSeries a)) :=
  hasSum_unitaryMatrixDualUniformCharacterSeries a h

/-- Pointwise evaluation of the uniformly convergent series is the scalar unconditional `tsum`. -/
theorem unitaryMatrixDualUniformCharacterSeries_apply
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (g : G) :
    unitaryMatrixDualUniformCharacterSeries a g =
      ∑' q, a q * unitaryMatrixDualCharacter q g := by
  rw [← compactContinuousMapEvaluation_apply g (unitaryMatrixDualUniformCharacterSeries a)]
  unfold unitaryMatrixDualUniformCharacterSeries
  rw [(compactContinuousMapEvaluation g).map_tsum
    (summable_unitaryMatrixDualContinuousCharacter_smul a h)]
  apply tsum_congr
  intro q
  rfl

/-- Evaluation at the identity is the exact dimension-weighted scalar `tsum`. -/
theorem unitaryMatrixDualUniformCharacterSeries_one
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    unitaryMatrixDualUniformCharacterSeries a (1 : G) =
      ∑' q, a q * (unitaryMatrixDualDimension q : ℂ) := by
  rw [unitaryMatrixDualUniformCharacterSeries_apply a h]
  apply tsum_congr
  intro q
  rw [unitaryMatrixDualCharacter_one]

/-- Exact Weierstrass bound for the global uniform norm of the character series. -/
theorem norm_unitaryMatrixDualUniformCharacterSeries_le
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    ‖unitaryMatrixDualUniformCharacterSeries a‖ ≤
      ∑' q, ‖a q‖ * (unitaryMatrixDualDimension q : ℝ) := by
  unfold unitaryMatrixDualUniformCharacterSeries
  have hn : Summable (fun q => ‖a q • unitaryMatrixDualContinuousCharacter q‖) := by
    simpa only [norm_smul, norm_unitaryMatrixDualContinuousCharacter] using h
  calc
    ‖∑' q, a q • unitaryMatrixDualContinuousCharacter q‖ ≤
        ∑' q, ‖a q • unitaryMatrixDualContinuousCharacter q‖ :=
      norm_tsum_le_tsum_norm hn
    _ = _ := by
      apply tsum_congr
      intro q
      rw [norm_smul, norm_unitaryMatrixDualContinuousCharacter]

/-- The uniformly summed selected-character series, packaged in the exact continuous-central
carrier. -/
noncomputable def unitaryMatrixDualUniformCentralCharacterSeries
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    continuousCentralFunctionStarSubalgebra G :=
  ⟨unitaryMatrixDualUniformCharacterSeries a, by
    intro g k
    rw [unitaryMatrixDualUniformCharacterSeries_apply a h,
      unitaryMatrixDualUniformCharacterSeries_apply a h]
    apply tsum_congr
    intro q
    rw [unitaryMatrixDualCharacter_conj]⟩

/-- The central packaging does not change the underlying continuous function. -/
@[simp]
theorem unitaryMatrixDualUniformCentralCharacterSeries_coe
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    (unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ)) =
      unitaryMatrixDualUniformCharacterSeries a :=
  rfl

end

end Mathematics
end YangMills
