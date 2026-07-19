/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.ContinuousMultilinearMapBasis

/-! Hostile probes for basis determination of continuous multilinear maps. -/

namespace YangMills.Mathematics.ContinuousMultilinearMapBasis.Probes

/-- Every finite arity, including zero, is covered by exact basis-tuple determination. -/
theorem exact_basis_determination
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (basis : Module.Basis ι ℝ E)
    (k : ℕ) (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (vanishes : ∀ indices : Fin k → ι, A (fun j => basis (indices j)) = 0) :
    A = 0 :=
  continuousMultilinearMap_eq_zero_of_basis_evaluation basis k A vanishes

/-- A nonzero map cannot hide behind zero values on every basis tuple. -/
theorem disconnected_nonzero_map_blocked
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (basis : Module.Basis ι ℝ E)
    {k : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F}
    (hA : A ≠ 0) :
    ∃ indices : Fin k → ι, A (fun j => basis (indices j)) ≠ 0 :=
  exists_basis_evaluation_ne_zero_of_ne_zero basis hA

/-- At arity zero the unique empty basis tuple still determines the map. -/
theorem exact_zero_arity
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (basis : Module.Basis ι ℝ E)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F)
    (emptyValue : A (fun i => nomatch i) = 0) :
    A = 0 := by
  apply continuousMultilinearMap_eq_zero_of_basis_evaluation basis 0 A
  intro indices
  have tupleEquality : (fun j => basis (indices j)) = (fun i : Fin 0 => nomatch i) :=
    Subsingleton.elim _ _
  rw [tupleEquality]
  exact emptyValue

end YangMills.Mathematics.ContinuousMultilinearMapBasis.Probes
