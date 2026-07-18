/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerConfigurationConcatenation

/-!
# Hostile probes for configuration concatenation

These probes ensure the second block is not overwritten by the first and that the raw tensor kernel
uses both exact factors. They do not assert that the raw kernel is Schwartz.
-/

namespace YangMills.Euclidean.SchwingerConfigurationConcatenation.Probes

/-- The first merged block is recovered at the exact `castAdd` index. -/
theorem exact_first_block
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) (i : Fin n) :
    euclideanConfigurationMerge d n m (x, y) (Fin.castAdd m i) = x i :=
  euclideanConfigurationMerge_castAdd_apply d n m x y i

/-- The second merged block is recovered at the exact `natAdd` offset. -/
theorem exact_second_block
    (d : EuclideanDimension) (n m : ℕ) (x : EuclideanNPointSpace d n)
    (y : EuclideanNPointSpace d m) (j : Fin m) :
    euclideanConfigurationMerge d n m (x, y) (Fin.natAdd n j) = y j :=
  euclideanConfigurationMerge_natAdd_apply d n m x y j

/-- The raw tensor kernel of two explicit nonzero bumps takes value one at the merged centers. -/
theorem positiveTimeBump_rawTensorKernel_at_centers
    (d : EuclideanDimension) :
    scalarSchwartzRawTensorKernel d (positiveTimeBumpSchwartz d)
        (positiveTimeBumpSchwartz d)
        (euclideanConfigurationMerge d 1 1
          (positiveTimeBumpCenter d, positiveTimeBumpCenter d)) = 1 := by
  rw [scalarSchwartzRawTensorKernel_merge]
  rw [positiveTimeBumpSchwartz_center]
  norm_num

/-- Zeroing the first factor zeroes the exact raw tensor value, so the first block cannot be ignored
by a malformed product implementation. -/
theorem zero_first_factor_rawTensorKernel
    (d : EuclideanDimension) {n m : ℕ} (g : ScalarSchwartzTestFunction d m)
    (x : EuclideanNPointSpace d n) (y : EuclideanNPointSpace d m) :
    scalarSchwartzRawTensorKernel d (0 : ScalarSchwartzTestFunction d n) g
        (euclideanConfigurationMerge d n m (x, y)) = 0 := by
  rw [scalarSchwartzRawTensorKernel_merge]
  simp

/-- Zeroing the second factor zeroes the exact raw tensor value, so the second block cannot be
ignored by a malformed product implementation. -/
theorem zero_second_factor_rawTensorKernel
    (d : EuclideanDimension) {n m : ℕ} (f : ScalarSchwartzTestFunction d n)
    (x : EuclideanNPointSpace d n) (y : EuclideanNPointSpace d m) :
    scalarSchwartzRawTensorKernel d f (0 : ScalarSchwartzTestFunction d m)
        (euclideanConfigurationMerge d n m (x, y)) = 0 := by
  rw [scalarSchwartzRawTensorKernel_merge]
  simp

/-- A claimed replacement of the nonzero two-bump kernel by zero contradicts exact center
evaluation. -/
theorem nonzero_rawTensorKernel_replacement_blocked
    (d : EuclideanDimension)
    (hzero : scalarSchwartzRawTensorKernel d (positiveTimeBumpSchwartz d)
      (positiveTimeBumpSchwartz d) = 0) : False := by
  have atCenters := congrArg (fun h : EuclideanNPointSpace d (1 + 1) → ℂ =>
    h (euclideanConfigurationMerge d 1 1
      (positiveTimeBumpCenter d, positiveTimeBumpCenter d))) hzero
  rw [positiveTimeBump_rawTensorKernel_at_centers] at atCenters
  simp at atCenters

end YangMills.Euclidean.SchwingerConfigurationConcatenation.Probes
