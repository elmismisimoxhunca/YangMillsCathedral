/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Dimensions.ThreeDimensionalSU2GaugeGroup

/-! Hostile probes for the exact three-dimensional SU(2) gauge-group contract. -/

namespace YangMills.Dimensions.ThreeDimensionalSU2GaugeGroup.Probes

open scoped Manifold ContDiff

noncomputable section

universe uE uGauge

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {GaugeGroup : Type uGauge} [Group GaugeGroup] [TopologicalSpace GaugeGroup]
    [T2Space GaugeGroup] [SecondCountableTopology GaugeGroup]
    [IsTopologicalGroup GaugeGroup] [ChartedSpace E GaugeGroup]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ GaugeGroup]
    (data : ThreeDimensionalSU2GaugeGroupData (E := E) (GaugeGroup := GaugeGroup))

include data in
/-- The gate exposes the exact continuous multiplicative equivalence to literal matrix SU(2). -/
theorem exact_su2_identification :
    Nonempty (GaugeGroup ≃ₜ* SpecialUnitaryTwo) :=
  ⟨data.identification⟩

include data in
/-- The gauge-group field retains the existing compact-simple Lie geometry contract. -/
theorem exact_compactSimple_geometry :
    Nonempty (Geometry.CompactSimpleGaugeGroupData GaugeGroup E) :=
  ⟨data.compactSimpleGaugeGroup⟩

include data in
/-- Hostile determinant probe: a U(2) element outside determinant one cannot pass as identified
SU(2). -/
theorem changed_determinant_blocked
    (g : GaugeGroup)
    (changed : Matrix.det
      ((data.identification g : SpecialUnitaryTwo) : Matrix (Fin 2) (Fin 2) ℂ) ≠ 1) : False :=
  changed (data.identified_mem_unitary_and_det_one g).2

include data in
/-- Hostile subgroup probe: the exact identification cannot omit an SU(2) element. -/
theorem nonsurjective_identification_blocked
    (missing : ¬ Function.Surjective data.identification) : False :=
  missing data.identification_surjective

include data in
/-- Hostile quotient probe: the exact identification cannot merge distinct gauge elements. -/
theorem noninjective_identification_blocked
    (missing : ¬ Function.Injective data.identification) : False :=
  missing data.identification_injective

include data in
/-- Hostile topology probe: neither direction of the SU(2) identification may be discontinuous. -/
theorem discontinuous_identification_blocked
    (missing : ¬(Continuous data.identification ∧ Continuous data.identification.symm)) : False :=
  missing data.identification_homeomorphic

end

end YangMills.Dimensions.ThreeDimensionalSU2GaugeGroup.Probes
