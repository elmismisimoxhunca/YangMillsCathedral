/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDualCharacterUniformSeries

/-!
# Hostile probes for uniformly summable selected-character series
-/

namespace YangMills
namespace Mathematics
namespace UnitaryMatrixDualCharacterUniformSeries
namespace Probes

noncomputable section

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Every selected matrix value is genuinely unitary. -/
theorem exact_selected_matrix_unitarity
    (q : UnitaryMatrixDual G) (g : G) :
    unitaryMatrixDualRepresentation q g ∈
      Matrix.unitaryGroup (Fin (unitaryMatrixDualDimension q)) ℂ :=
  unitaryMatrixDualRepresentation_mem_unitaryGroup q g

/-- Every selected character obeys the exact dimension bound. -/
theorem exact_character_dimension_bound
    (q : UnitaryMatrixDual G) (g : G) :
    ‖unitaryMatrixDualCharacter q g‖ ≤ (unitaryMatrixDualDimension q : ℝ) :=
  norm_unitaryMatrixDualCharacter_le_dimension q g

/-- Hostile pointwise bound probe: strict violation of the dimension bound is contradictory. -/
theorem character_dimension_bound_violation_blocked
    (q : UnitaryMatrixDual G) (g : G)
    (violated : (unitaryMatrixDualDimension q : ℝ) <
      ‖unitaryMatrixDualCharacter q g‖) : False :=
  (not_lt_of_ge (norm_unitaryMatrixDualCharacter_le_dimension q g)) violated

/-- Character evaluation at the identity is exactly the matrix dimension. -/
theorem exact_character_identity_value
    (q : UnitaryMatrixDual G) :
    unitaryMatrixDualCharacter q (1 : G) = (unitaryMatrixDualDimension q : ℂ) :=
  unitaryMatrixDualCharacter_one q

/-- Hostile identity probe: changing the identity character value is contradictory. -/
theorem changed_character_identity_value_blocked
    (q : UnitaryMatrixDual G) {changed : ℂ}
    (hchanged : changed ≠ (unitaryMatrixDualDimension q : ℂ))
    (changedValue : unitaryMatrixDualCharacter q (1 : G) = changed) : False := by
  apply hchanged
  rw [← changedValue]
  exact unitaryMatrixDualCharacter_one q

variable [CompactSpace G]

/-- The uniform character norm is exactly the dimension, so the pointwise bound is sharp. -/
theorem exact_uniform_character_norm
    (q : UnitaryMatrixDual G) :
    ‖unitaryMatrixDualContinuousCharacter q‖ = (unitaryMatrixDualDimension q : ℝ) :=
  norm_unitaryMatrixDualContinuousCharacter q

/-- Hostile norm probe: changing the sharp uniform character norm is contradictory. -/
theorem changed_uniform_character_norm_blocked
    (q : UnitaryMatrixDual G) {changed : ℝ}
    (hchanged : changed ≠ (unitaryMatrixDualDimension q : ℝ))
    (changedNorm : ‖unitaryMatrixDualContinuousCharacter q‖ = changed) : False := by
  apply hchanged
  rw [← changedNorm]
  exact norm_unitaryMatrixDualContinuousCharacter q

/-- Weighted dimension summability gives unconditional summability in `C(G, ℂ)`. -/
theorem exact_weighted_uniform_summability
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Summable (fun q => a q • unitaryMatrixDualContinuousCharacter q) :=
  summable_unitaryMatrixDualContinuousCharacter_smul a h

/-- The net over every finite selected-class set converges in the global uniform norm. -/
theorem exact_uniform_finset_net_convergence
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, a q • unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualUniformCharacterSeries a)) :=
  tendsto_finsetSum_unitaryMatrixDualContinuousCharacter a h

/-- Hostile convergence probe: failure of the exact uniform finite-subset net is contradictory. -/
theorem failed_uniform_finset_net_convergence_blocked
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (failed : ¬ Filter.Tendsto (fun s : Finset (UnitaryMatrixDual G) =>
      ∑ q ∈ s, a q • unitaryMatrixDualContinuousCharacter q)
      Filter.atTop (nhds (unitaryMatrixDualUniformCharacterSeries a))) : False :=
  failed (tendsto_finsetSum_unitaryMatrixDualContinuousCharacter a h)

/-- Pointwise series evaluation has the exact scalar `tsum` orientation. -/
theorem exact_uniform_series_pointwise_value
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (g : G) :
    unitaryMatrixDualUniformCharacterSeries a g =
      ∑' q, a q * unitaryMatrixDualCharacter q g :=
  unitaryMatrixDualUniformCharacterSeries_apply a h g

/-- Identity evaluation has the exact dimension-weighted `tsum`. -/
theorem exact_uniform_series_identity_value
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    unitaryMatrixDualUniformCharacterSeries a (1 : G) =
      ∑' q, a q * (unitaryMatrixDualDimension q : ℂ) :=
  unitaryMatrixDualUniformCharacterSeries_one a h

/-- The exact weighted Weierstrass bound controls the global uniform norm. -/
theorem exact_uniform_series_norm_bound
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ))) :
    ‖unitaryMatrixDualUniformCharacterSeries a‖ ≤
      ∑' q, ‖a q‖ * (unitaryMatrixDualDimension q : ℝ) :=
  norm_unitaryMatrixDualUniformCharacterSeries_le a h

/-- Hostile Weierstrass probe: strict violation of the global norm bound is contradictory. -/
theorem uniform_series_norm_bound_violation_blocked
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (violated : (∑' q, ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)) <
      ‖unitaryMatrixDualUniformCharacterSeries a‖) : False :=
  (not_lt_of_ge (norm_unitaryMatrixDualUniformCharacterSeries_le a h)) violated

/-- The uniformly convergent series is central under the same unchanged summability premise. -/
theorem exact_uniform_series_centrality
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (g k : G) :
    (unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ)) (k * g * k⁻¹) =
      (unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ)) g :=
  (unitaryMatrixDualUniformCentralCharacterSeries a h).property g k

/-- Hostile centrality probe: failure of conjugation invariance is contradictory. -/
theorem failed_uniform_series_centrality_blocked
    (a : UnitaryMatrixDual G → ℂ)
    (h : Summable (fun q => ‖a q‖ * (unitaryMatrixDualDimension q : ℝ)))
    (g k : G)
    (failed : (unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ))
        (k * g * k⁻¹) ≠
      (unitaryMatrixDualUniformCentralCharacterSeries a h : C(G, ℂ)) g) : False :=
  failed ((unitaryMatrixDualUniformCentralCharacterSeries a h).property g k)

end

end Probes
end UnitaryMatrixDualCharacterUniformSeries
end Mathematics
end YangMills
