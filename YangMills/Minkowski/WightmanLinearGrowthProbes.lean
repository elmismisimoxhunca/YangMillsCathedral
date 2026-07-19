/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanLinearGrowth

/-!
# Hostile probes for OS-II Wightman linear growth

These probes lock the flattened positive coordinate weight, exact Wightman distribution, common
positive order, `n²` coefficient growth, and least-upper-bound control. They do not construct a
Wightman theory or reconstruction.
-/

namespace YangMills.Minkowski.WightmanLinearGrowth.Probes

open YangMills
open YangMills.Minkowski

/-- The Wightman Schwartz square is the sum over every point and coordinate, not the outer Pi norm
and not the indefinite Minkowski form. -/
example {n : ℕ}
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) :
    wightmanFourDimensionalConfigurationSquaredNorm x =
      ∑ point, ∑ coordinate, (x point coordinate) ^ 2 :=
  rfl

/-- The exact printed term uses the flattened square and coordinate multi-index derivative. -/
example {n : ℕ} (order : ℕ) (α : FourDimensionalMultiIndex n)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) :
    osIIWightmanWeightedDerivativeTerm order α f x =
      Real.rpow (1 + wightmanFourDimensionalConfigurationSquaredNorm x)
          ((order : ℝ) / 2) *
        ‖wightmanFourDimensionalMultiIndexDerivative α f x‖ :=
  rfl

/-- Every term below the same exact order is controlled. -/
example {n order : ℕ} (data : OSIIWightmanPrintedSchwartzControlData n order)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n) (hα : fourDimensionalMultiIndexOrder α ≤ order)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) :
    osIIWightmanWeightedDerivativeTerm order α f x ≤ data.control f :=
  data.weightedDerivative_le f α hα x

/-- Two controls satisfying the exact universal property cannot disagree. -/
example {n order : ℕ} (first second : OSIIWightmanPrintedSchwartzControlData n order) :
    first.control = second.control :=
  first.control_unique second

/-- A positive exact term blocks a disconnected zero control. -/
example {n order : ℕ} (data : OSIIWightmanPrintedSchwartzControlData n order)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n) (hα : fourDimensionalMultiIndexOrder α ≤ order)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n)
    (positive : 0 < osIIWightmanWeightedDerivativeTerm order α f x) :
    data.control f ≠ 0 :=
  data.control_ne_zero_of_term_pos f α hα x positive

/-- The source's positive coefficient and exact `n²` upper bound remain visible. -/
example (growth : OSIIWightmanLinearGrowthCoefficientData) (n : PositiveArity) :
    0 < growth.coefficient n ∧
      growth.coefficient n ≤ growth.alpha * growth.beta ^ (n.value ^ 2) :=
  ⟨growth.coefficient_pos n, growth.coefficient_bound n⟩

/-- The right-hand side cannot collapse to zero or negative at any positive arity. -/
example (growth : OSIIWightmanLinearGrowthCoefficientData) (n : PositiveArity) :
    0 < growth.alpha * growth.beta ^ (n.value ^ 2) :=
  growth.bound_positive n

variable
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    {full : ScalarWightmanJointTemperedCorrelatorData fieldData}
    (growth : OSIIWightmanLinearGrowthData full)

/-- One positive order controls every exact positive arity. -/
example : 0 < growth.order :=
  growth.order_positive

/-- Equation (4.3) is wired to the exact existing full Wightman distribution, not a disconnected
functional family. -/
example (n : PositiveArity)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n.value) :
    ‖full.nPointDistribution n.value f‖ ≤
      growth.growth.coefficient n * (growth.printedControl n).control f :=
  growth.bound n f

end YangMills.Minkowski.WightmanLinearGrowth.Probes
