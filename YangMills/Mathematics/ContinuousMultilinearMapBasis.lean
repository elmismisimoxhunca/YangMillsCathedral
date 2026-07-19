/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# Continuous multilinear maps determined on basis tuples

A finite-arity continuous multilinear map is zero when it vanishes on every tuple of vectors from
an arbitrary algebraic basis. The proof is independent of finite dimensionality and is reusable
outside Yang–Mills.
-/

namespace YangMills.Mathematics

/-- A continuous `k`-linear map that vanishes on every basis tuple is the zero map. -/
theorem continuousMultilinearMap_eq_zero_of_basis_evaluation
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (basis : Module.Basis ι ℝ E) :
    ∀ (k : ℕ) (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F),
      (∀ indices : Fin k → ι, A (fun j => basis (indices j)) = 0) → A = 0 := by
  intro k A h
  have underlyingZero : A.toMultilinearMap = 0 := by
    apply Module.Basis.ext_multilinear (fun _ : Fin k => basis)
    intro indices
    exact h indices
  apply ContinuousMultilinearMap.ext
  intro vectors
  exact congrArg
    (fun L : MultilinearMap ℝ (fun _ : Fin k => E) F => L vectors) underlyingZero

/-- Contrapositive anti-vacuity form: a nonzero multilinear map is detected by a basis tuple. -/
theorem exists_basis_evaluation_ne_zero_of_ne_zero
    {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (basis : Module.Basis ι ℝ E)
    {k : ℕ} {A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F}
    (hA : A ≠ 0) :
    ∃ indices : Fin k → ι, A (fun j => basis (indices j)) ≠ 0 := by
  by_contra absent
  push Not at absent
  exact hA (continuousMultilinearMap_eq_zero_of_basis_evaluation basis k A absent)

end YangMills.Mathematics
