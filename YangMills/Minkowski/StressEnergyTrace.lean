/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Foundation.Signatures
import YangMills.Minkowski.LocalStressEnergyTensor

/-!
# Mostly-minus trace of the exact stress-energy tensor

Blaschke–Gieres–Reboud–Schweda 2016, §2.2.1, equation (2.11), identifies the
four-dimensional classical Yang–Mills stress tensor as traceless. This module only defines the
quantum trace carrier by contracting the already designated same-family stress components with the
project's mostly-minus Minkowski metric. It creates neither a new label nor a second operator family,
and it does not assert classical tracelessness or a quantum anomaly identity.
-/

namespace YangMills.Minkowski

open scoped BigOperators Manifold ContDiff

noncomputable section

/-- The mostly-minus trace, formed directly from the exact existing diagonal stress-component
operators. It introduces no observable label and no second operator family. -/
def stressTensorTraceOperator
    {d : EuclideanDimension} {liftGroup : Type*}
    [Group liftGroup] [TopologicalSpace liftGroup] [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData d liftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) : D.domain :=
  ∑ μ, (d.minkowskiWeight μ : ℂ) •
    family.operator (stress.componentLabel μ μ) f ψ

/-- In four dimensions the direct mostly-minus contraction is exactly
`T⁰⁰ - T¹¹ - T²² - T³³`. -/
theorem stressTensorTraceOperator_four_expansion
    {liftGroup : Type*}
    [Group liftGroup] [TopologicalSpace liftGroup] [IsTopologicalGroup liftGroup]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four liftGroup}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (stress : LocalStressEnergyTensorData family)
    (f : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.four)
    (ψ : D.domain) :
    stressTensorTraceOperator stress f ψ =
      family.operator (stress.componentLabel
        (⟨0, by decide⟩ : EuclideanDimension.four.CoordinateIndex)
        (⟨0, by decide⟩ : EuclideanDimension.four.CoordinateIndex)) f ψ -
      family.operator (stress.componentLabel
        (⟨1, by decide⟩ : EuclideanDimension.four.CoordinateIndex)
        (⟨1, by decide⟩ : EuclideanDimension.four.CoordinateIndex)) f ψ -
      family.operator (stress.componentLabel
        (⟨2, by decide⟩ : EuclideanDimension.four.CoordinateIndex)
        (⟨2, by decide⟩ : EuclideanDimension.four.CoordinateIndex)) f ψ -
      family.operator (stress.componentLabel
        (⟨3, by decide⟩ : EuclideanDimension.four.CoordinateIndex)
        (⟨3, by decide⟩ : EuclideanDimension.four.CoordinateIndex)) f ψ := by
  unfold stressTensorTraceOperator
  change (∑ μ : Fin 4, (((if μ.val = 0 then 1 else -1 : ℝ) : ℂ) •
    family.operator (stress.componentLabel μ μ) f ψ)) = _
  rw [Fin.sum_univ_four]
  norm_num
  abel

end

end YangMills.Minkowski
