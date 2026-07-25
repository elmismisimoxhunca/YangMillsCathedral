/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Matrix
import YangMills.Geometry.LieGroup

/-!
# Exact SU(2) gauge-group contract for the three-dimensional truth teller

Hall defines `SU(n)` as the group of unitary `n × n` complex matrices with determinant one
(Hall 2000, §2.4, extracted source lines 582--609). This file fixes `n = 2` literally using
Mathlib's `Matrix.specialUnitaryGroup (Fin 2) ℂ`; no unspecified compact-simple group or opaque
isomorphism class is called `SU(2)`.

A future geometric gauge carrier may have a separately convenient manifold presentation. The
source-facing bridge therefore requires an explicit continuous multiplicative equivalence between
that carrier and the exact matrix group, in addition to the project's existing compact-simple Lie
geometry data. No such carrier, equivalence, compactness proof for Mathlib's raw subtype, or
Yang--Mills theory is constructed here.
-/

namespace YangMills.Dimensions

open scoped Manifold ContDiff

noncomputable section

universe uE uGauge

/-- Literal algebraic special unitary group of two-by-two complex matrices. -/
abbrev SpecialUnitaryTwo := Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- Exact SU(2) identification for one geometric gauge carrier. The continuous multiplicative
equivalence prevents a generic compact-simple group from silently filling the SU(2) gate. -/
structure ThreeDimensionalSU2GaugeGroupData
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace E GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ GaugeGroup] where
  compactSimpleGaugeGroup : Geometry.CompactSimpleGaugeGroupData GaugeGroup E
  identification : GaugeGroup ≃ₜ* SpecialUnitaryTwo

namespace ThreeDimensionalSU2GaugeGroupData

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace E GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ GaugeGroup]

/-- The exact matrix target has size two, not a caller-selected rank. -/
theorem exact_matrix_size
    (_data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup)) :
    Fintype.card (Fin 2) = 2 := by simp

/-- Every identified gauge element is literally a unitary two-by-two matrix of determinant one. -/
theorem identified_mem_unitary_and_det_one
    (data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup))
    (g : GaugeGroup) :
    ((data.identification g : SpecialUnitaryTwo) : Matrix (Fin 2) (Fin 2) ℂ) ∈
        Matrix.unitaryGroup (Fin 2) ℂ ∧
      Matrix.det
        ((data.identification g : SpecialUnitaryTwo) : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  Matrix.mem_specialUnitaryGroup_iff.mp (data.identification g).property

/-- The exact SU(2) identification is surjective, so it does not select only a proper subgroup. -/
theorem identification_surjective
    (data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup)) :
    Function.Surjective data.identification :=
  data.identification.surjective

/-- The exact SU(2) identification is injective, ruling out a nontrivial covering kernel. -/
theorem identification_injective
    (data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup)) :
    Function.Injective data.identification :=
  data.identification.injective

/-- Both directions of the exact gauge-group identification are continuous. -/
theorem identification_homeomorphic
    (data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup)) :
    Continuous data.identification ∧ Continuous data.identification.symm :=
  ⟨data.identification.toHomeomorph.continuous,
    data.identification.toHomeomorph.continuous_symm⟩

end ThreeDimensionalSU2GaugeGroupData

end

end YangMills.Dimensions
