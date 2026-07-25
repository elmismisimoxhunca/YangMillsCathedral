/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerTestSequence

/-!
# Concatenating Euclidean point configurations

The Osterwalder–Schrader sequence product combines an `n`-point test and an `m`-point test into an
`(n+m)`-point test. Before proving that tensor products remain Schwartz, this module constructs the
exact continuous linear configuration split/merge maps and the underlying pointwise scalar product
kernel.

The first block occupies `Fin.castAdd m`; the second occupies `Fin.natAdd n`. The raw kernel is not
claimed to be a bundled Schwartz map. Proving its Schwartz regularity and continuity is the next
reusable mathematical obligation; no sequence product or `(E2)` is defined here.
-/

namespace YangMills

/-- Split an `(n+m)`-point Euclidean configuration into its first `n` and last `m` points. -/
noncomputable def euclideanConfigurationSplit
    (d : EuclideanDimension) (n m : ℕ) :
    EuclideanNPointSpace d (n + m) ≃L[ℝ]
      EuclideanNPointSpace d n × EuclideanNPointSpace d m :=
  (ContinuousLinearEquiv.piCongrLeft ℝ
    (fun _ : Fin (n + m) => d.Spacetime) (finSumFinEquiv (m := n) (n := m))).symm |>.trans
  (ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin n) (Fin m)
    (fun _ => d.Spacetime))

/-- The first split block uses exactly `Fin.castAdd m`. -/
theorem euclideanConfigurationSplit_left_apply
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d (n + m))
    (i : Fin n) :
    (euclideanConfigurationSplit d n m x).1 i = x (Fin.castAdd m i) := by
  change ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => d.Spacetime))
    ((Equiv.piCongrLeft (fun _ : Fin (n + m) => d.Spacetime) finSumFinEquiv).symm x)).1 i = _
  rfl

/-- The second split block uses exactly `Fin.natAdd n`. -/
theorem euclideanConfigurationSplit_right_apply
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d (n + m))
    (j : Fin m) :
    (euclideanConfigurationSplit d n m x).2 j = x (Fin.natAdd n j) := by
  change ((Equiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => d.Spacetime))
    ((Equiv.piCongrLeft (fun _ : Fin (n + m) => d.Spacetime) finSumFinEquiv).symm x)).2 j = _
  rfl

/-- Merge an `n`-point and an `m`-point configuration into one `(n+m)`-point configuration. -/
noncomputable def euclideanConfigurationMerge
    (d : EuclideanDimension) (n m : ℕ) :
    (EuclideanNPointSpace d n × EuclideanNPointSpace d m) ≃L[ℝ]
      EuclideanNPointSpace d (n + m) :=
  (euclideanConfigurationSplit d n m).symm

/-- Merging preserves every coordinate of the first block. -/
theorem euclideanConfigurationMerge_castAdd_apply
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) (i : Fin n) :
    euclideanConfigurationMerge d n m (x, y) (Fin.castAdd m i) = x i := by
  have h := congrArg (fun z => z.1 i)
    ((euclideanConfigurationSplit d n m).apply_symm_apply (x, y))
  rw [euclideanConfigurationSplit_left_apply] at h
  exact h

/-- Merging preserves every coordinate of the second block at the exact offset. -/
theorem euclideanConfigurationMerge_natAdd_apply
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) (j : Fin m) :
    euclideanConfigurationMerge d n m (x, y) (Fin.natAdd n j) = y j := by
  have h := congrArg (fun z => z.2 j)
    ((euclideanConfigurationSplit d n m).apply_symm_apply (x, y))
  rw [euclideanConfigurationSplit_right_apply] at h
  exact h

/-- The raw scalar tensor kernel before it is packaged as an `(n+m)`-point Schwartz test. -/
noncomputable def scalarSchwartzRawTensorKernel
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) : EuclideanNPointSpace d (n + m) → ℂ :=
  fun x => f (euclideanConfigurationSplit d n m x).1 *
    g (euclideanConfigurationSplit d n m x).2

/-- The raw tensor kernel evaluates through the exact configuration split. -/
@[simp] theorem scalarSchwartzRawTensorKernel_apply
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) (x : EuclideanNPointSpace d (n + m)) :
    scalarSchwartzRawTensorKernel d f g x =
      f (euclideanConfigurationSplit d n m x).1 *
        g (euclideanConfigurationSplit d n m x).2 :=
  rfl

/-- Evaluation after exact merging is the product of the two original evaluations. -/
@[simp] theorem scalarSchwartzRawTensorKernel_merge
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (g : ScalarSchwartzTestFunction d m) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) :
    scalarSchwartzRawTensorKernel d f g
        (euclideanConfigurationMerge d n m (x, y)) = f x * g y := by
  simp only [scalarSchwartzRawTensorKernel_apply]
  change f ((euclideanConfigurationSplit d n m)
      ((euclideanConfigurationSplit d n m).symm (x, y))).1 *
    g ((euclideanConfigurationSplit d n m)
      ((euclideanConfigurationSplit d n m).symm (x, y))).2 = _
  rw [(euclideanConfigurationSplit d n m).apply_symm_apply]

end YangMills
