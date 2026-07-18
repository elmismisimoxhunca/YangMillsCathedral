/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.QuadraticTopology

/-!
# Complexified Minkowski tube geometry

Streater–Wightman printed p. 114, Theorem 3-5, places relative-coordinate vacuum functions on the
tube `ξ - iη` with every `η` in the open forward cone. This module constructs that exact-sign open
domain in dimensions 1–4 and proves it nonempty with an explicit negative-imaginary time point.

It defines no holomorphic function, boundary value, correlator continuation, reconstruction, or
physical inhabitant.
-/

namespace YangMills.Minkowski

/-- Complexified coordinate spacetime, with no Euclidean identification. -/
abbrev ComplexifiedSpacetime (d : EuclideanDimension) := d.CoordinateIndex → ℂ

/-- Coordinatewise imaginary part as a real Minkowski vector. -/
def complexifiedSpacetimeImaginaryPart
    {d : EuclideanDimension} (z : ComplexifiedSpacetime d) : Spacetime d :=
  fun i => (z i).im

/-- Imaginary-part extraction is continuous. -/
theorem continuous_complexifiedSpacetimeImaginaryPart
    (d : EuclideanDimension) :
    Continuous (complexifiedSpacetimeImaginaryPart (d := d)) := by
  apply continuous_pi
  intro i
  exact Complex.continuous_im.comp (continuous_apply i)

/-- Interior of the mostly-minus future cone. -/
def openForwardMomentumCone (d : EuclideanDimension) : Set (Spacetime d) :=
  {p | 0 < p d.timeIndex ∧ 0 < d.minkowskiQuadraticForm p}

/-- The open future cone is topologically open. -/
theorem isOpen_openForwardMomentumCone (d : EuclideanDimension) :
    IsOpen (openForwardMomentumCone d) := by
  exact (isOpen_lt continuous_const (continuous_apply d.timeIndex)).inter
    (isOpen_lt continuous_const (continuous_minkowskiQuadraticForm d))

/-- The relative-coordinate backward tube `ξ - iη`, with every `η` in the open future cone. -/
def wightmanBackwardTube (d : EuclideanDimension) (n : ℕ) :
    Set (Fin n → ComplexifiedSpacetime d) :=
  {z | ∀ j, -complexifiedSpacetimeImaginaryPart (z j) ∈ openForwardMomentumCone d}

/-- Every finite-arity backward tube is open. -/
theorem isOpen_wightmanBackwardTube (d : EuclideanDimension) (n : ℕ) :
    IsOpen (wightmanBackwardTube d n) := by
  have hopen : ∀ j : Fin n, IsOpen
      {z : Fin n → ComplexifiedSpacetime d |
        -complexifiedSpacetimeImaginaryPart (z j) ∈ openForwardMomentumCone d} := by
    intro j
    apply (isOpen_openForwardMomentumCone d).preimage
    exact (continuous_complexifiedSpacetimeImaginaryPart d).comp
      (continuous_apply j) |>.neg
  have hinter := isOpen_iInter_of_finite hopen
  have hset : wightmanBackwardTube d n = ⋂ j : Fin n,
      {z : Fin n → ComplexifiedSpacetime d |
        -complexifiedSpacetimeImaginaryPart (z j) ∈ openForwardMomentumCone d} := by
    ext z
    simp [wightmanBackwardTube]
  rw [hset]
  exact hinter

/-- Standard tube point with every relative coordinate equal to negative imaginary unit time. -/
def standardWightmanBackwardTubePoint
    (d : EuclideanDimension) (n : ℕ) : Fin n → ComplexifiedSpacetime d :=
  fun _ i => if i = d.timeIndex then -Complex.I else 0

/-- The standard point has future-directed negative imaginary part. -/
theorem standardWightmanBackwardTubePoint_mem
    (d : EuclideanDimension) (n : ℕ) :
    standardWightmanBackwardTubePoint d n ∈ wightmanBackwardTube d n := by
  intro j
  constructor
  · simp [standardWightmanBackwardTubePoint,
      complexifiedSpacetimeImaginaryPart, EuclideanDimension.timeIndex]
  · have hvalue :
        -complexifiedSpacetimeImaginaryPart
          (standardWightmanBackwardTubePoint d n j) =
          d.basisVector d.timeIndex := by
      funext i
      by_cases hi : i = d.timeIndex
      · subst i
        simp [standardWightmanBackwardTubePoint,
          complexifiedSpacetimeImaginaryPart, EuclideanDimension.basisVector]
      · simp [standardWightmanBackwardTubePoint,
          complexifiedSpacetimeImaginaryPart, EuclideanDimension.basisVector, hi]
    rw [hvalue, d.minkowskiQuadraticForm_time_basisVector]
    norm_num

/-- Every finite-arity backward tube is inhabited. -/
theorem wightmanBackwardTube_nonempty
    (d : EuclideanDimension) (n : ℕ) :
    (wightmanBackwardTube d n).Nonempty :=
  ⟨standardWightmanBackwardTubePoint d n,
    standardWightmanBackwardTubePoint_mem d n⟩

/-- At positive arity the zero complex configuration is not in the strict tube. -/
theorem zero_not_mem_wightmanBackwardTube
    (d : EuclideanDimension) {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → ComplexifiedSpacetime d) ∉ wightmanBackwardTube d n := by
  intro hzero
  let j : Fin n := ⟨0, hn⟩
  have hj := hzero j
  simpa [openForwardMomentumCone, complexifiedSpacetimeImaginaryPart] using hj.1

end YangMills.Minkowski
