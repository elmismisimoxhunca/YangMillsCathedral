/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.SchwartzTensorProduct
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Schwartz tensors on finite configurations

Reusable, signature-neutral infrastructure for finite configurations `Fin n → E`. It constructs
exact continuous-linear block splitting, zero- and one-arity Schwartz tests, concatenated tensor
products, and pure tensors of arbitrary finite families. Euclidean Schwinger and Minkowski Wightman
surfaces can share this mathematics without importing or identifying one another's physical APIs.
-/

open scoped SchwartzMap

namespace YangMills.Mathematics

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An `n`-point configuration in a real normed coordinate space. -/
abbrev FiniteConfiguration (n : ℕ) := Fin n → E

/-- Split an `(n+m)`-configuration into its exact first and last blocks. -/
noncomputable def finiteConfigurationSplit (n m : ℕ) :
    FiniteConfiguration E (n + m) ≃L[ℝ]
      FiniteConfiguration E n × FiniteConfiguration E m :=
  (ContinuousLinearEquiv.piCongrLeft ℝ
    (fun _ : Fin (n + m) => E) (finSumFinEquiv (m := n) (n := m))).symm |>.trans
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin m) (fun _ => E))

/-- Exact first-block coordinate formula. -/
theorem finiteConfigurationSplit_left_apply
    (n m : ℕ) (x : FiniteConfiguration E (n + m)) (i : Fin n) :
    (finiteConfigurationSplit E n m x).1 i = x (Fin.castAdd m i) := by
  rfl

/-- Exact last-block coordinate formula. -/
theorem finiteConfigurationSplit_right_apply
    (n m : ℕ) (x : FiniteConfiguration E (n + m)) (j : Fin m) :
    (finiteConfigurationSplit E n m x).2 j = x (Fin.natAdd n j) := by
  rfl

/-- Merge two exact finite configuration blocks. -/
noncomputable def finiteConfigurationMerge (n m : ℕ) :
    (FiniteConfiguration E n × FiniteConfiguration E m) ≃L[ℝ]
      FiniteConfiguration E (n + m) :=
  (finiteConfigurationSplit E n m).symm

/-- Concatenated scalar Schwartz tensor on finite configurations. -/
noncomputable def scalarSchwartzTensorProductOnFiniteConfiguration
    {n m : ℕ} (f : 𝓢(FiniteConfiguration E n, ℂ))
    (g : 𝓢(FiniteConfiguration E m, ℂ)) :
    𝓢(FiniteConfiguration E (n + m), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (finiteConfigurationSplit E n m)
    (scalarSchwartzTensorProduct f g)

/-- Exact split formula for a concatenated tensor. -/
@[simp] theorem scalarSchwartzTensorProductOnFiniteConfiguration_apply
    {n m : ℕ} (f : 𝓢(FiniteConfiguration E n, ℂ))
    (g : 𝓢(FiniteConfiguration E m, ℂ))
    (x : FiniteConfiguration E (n + m)) :
    scalarSchwartzTensorProductOnFiniteConfiguration E f g x =
      f (finiteConfigurationSplit E n m x).1 *
        g (finiteConfigurationSplit E n m x).2 :=
  rfl

/-- A scalar as a Schwartz function on the compact zero-point configuration. -/
noncomputable def scalarZeroConfigurationSchwartz (c : ℂ) :
    𝓢(FiniteConfiguration E 0, ℂ) := by
  let f : FiniteConfiguration E 0 → ℂ := fun _ => c
  exact (HasCompactSupport.of_compactSpace f).toSchwartzMap contDiff_const

/-- Exact zero-configuration evaluation. -/
@[simp] theorem scalarZeroConfigurationSchwartz_apply
    (c : ℂ) (x : FiniteConfiguration E 0) :
    scalarZeroConfigurationSchwartz E c x = c :=
  rfl

/-- Lift one scalar Schwartz test to the one-point configuration. -/
noncomputable def scalarOneConfigurationSchwartz (f : 𝓢(E, ℂ)) :
    𝓢(FiniteConfiguration E 1, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => E)) f

/-- Exact one-configuration evaluation. -/
@[simp] theorem scalarOneConfigurationSchwartz_apply
    (f : 𝓢(E, ℂ)) (x : FiniteConfiguration E 1) :
    scalarOneConfigurationSchwartz E f x = f (x 0) :=
  rfl

/-- Pure Schwartz tensor of a finite family of one-point tests, in coordinate order. -/
noncomputable def scalarSchwartzPureTensor :
    (n : ℕ) → (Fin n → 𝓢(E, ℂ)) → 𝓢(FiniteConfiguration E n, ℂ)
  | 0, _ => scalarZeroConfigurationSchwartz E 1
  | n + 1, f =>
      scalarSchwartzTensorProductOnFiniteConfiguration E
        (scalarSchwartzPureTensor n (fun i => f i.castSucc))
        (scalarOneConfigurationSchwartz E (f (Fin.last n)))

/-- The empty pure tensor is the scalar unit. -/
@[simp] theorem scalarSchwartzPureTensor_zero
    (f : Fin 0 → 𝓢(E, ℂ)) :
    scalarSchwartzPureTensor E 0 f = scalarZeroConfigurationSchwartz E 1 :=
  rfl

/-- Successor pure tensors split the initial `n`-coordinate block from the final singleton. -/
@[simp] theorem scalarSchwartzPureTensor_succ
    (n : ℕ) (f : Fin (n + 1) → 𝓢(E, ℂ)) :
    scalarSchwartzPureTensor E (n + 1) f =
      scalarSchwartzTensorProductOnFiniteConfiguration E
        (scalarSchwartzPureTensor E n (fun i => f i.castSucc))
        (scalarOneConfigurationSchwartz E (f (Fin.last n))) :=
  rfl

/-- Pure tensors evaluate as the coordinatewise finite product. -/
theorem scalarSchwartzPureTensor_apply
    (n : ℕ) (f : Fin n → 𝓢(E, ℂ)) (x : FiniteConfiguration E n) :
    scalarSchwartzPureTensor E n f x = ∏ i, f i (x i) := by
  induction n with
  | zero =>
      simp [scalarSchwartzPureTensor]
  | succ n ih =>
      rw [scalarSchwartzPureTensor_succ,
        scalarSchwartzTensorProductOnFiniteConfiguration_apply]
      rw [ih]
      rw [Fin.prod_univ_castSucc]
      rfl

end YangMills.Mathematics
