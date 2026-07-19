/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.OSOrderedFourDimensionalMultiIndex
import YangMills.Minkowski.WightmanJointTemperedCorrelators

/-!
# OS-II Wightman linear growth `(R0′)`

Osterwalder–Schrader II, printed p. 287 equation (4.3), strengthens the reconstructed Wightman
output by one common positive Schwartz order `w` and positive coefficients `ωₙ` satisfying
`ωₙ ≤ α β^(n²)` and `|Wₙ(f)| ≤ ωₙ |f|_{n,w}`.

This module formalizes the exact flattened `ℝ^(4n)` coordinate-square and coordinate multi-index
control on the existing full Wightman Schwartz carrier. It is an uninhabited output requirement,
not a reconstruction theorem, tube-growth condition, theory construction, or mass-gap statement.
-/

namespace YangMills.Minkowski

open scoped BigOperators

noncomputable section

/-- Exact point/coordinate basis direction in full four-dimensional Minkowski configuration space.
The Schwartz control is positive-definite coordinate geometry and does not use the Minkowski
quadratic form. -/
def wightmanFourDimensionalCoordinateBasis
    (n : ℕ) (index : FourDimensionalPointCoordinateIndex n) :
    Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n :=
  fun point => if point = index.1 then
    EuclideanDimension.basisVector EuclideanDimension.four index.2 else 0

/-- Exact repeated coordinate-basis tuple for a four-dimensional multi-index. -/
def wightmanFourDimensionalMultiIndexDirections
    {n : ℕ} (α : FourDimensionalMultiIndex n) :
    Fin (fourDimensionalMultiIndexOrder α) →
      Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n :=
  fun slot => wightmanFourDimensionalCoordinateBasis n
    (fourDimensionalMultiIndexRepeatedCoordinate α slot)

/-- Exact Wightman coordinate partial derivative `D^α`. -/
def wightmanFourDimensionalMultiIndexDerivative
    {n : ℕ} (α : FourDimensionalMultiIndex n)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) : ℂ :=
  iteratedFDeriv ℝ (fourDimensionalMultiIndexOrder α)
    (f : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n → ℂ) x
    (wightmanFourDimensionalMultiIndexDirections α)

/-- Exact flattened coordinate square `x² = ∑ᵢ∑μ (xᵢ^μ)²` on Minkowski-coordinate `ℝ^(4n)`.
This is the positive Schwartz weight, not the indefinite Minkowski quadratic form and not the outer
Pi supremum norm. -/
def wightmanFourDimensionalConfigurationSquaredNorm
    {n : ℕ} (x : Mathematics.FiniteConfiguration
      (Spacetime EuclideanDimension.four) n) : ℝ :=
  ∑ point, ∑ coordinate, (x point coordinate) ^ 2

/-- One exact weighted derivative term in OS-II's printed Wightman Schwartz control. -/
noncomputable def osIIWightmanWeightedDerivativeTerm
    {n : ℕ} (order : ℕ) (α : FourDimensionalMultiIndex n)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n) : ℝ :=
  Real.rpow (1 + wightmanFourDimensionalConfigurationSquaredNorm x)
      ((order : ℝ) / 2) *
    ‖wightmanFourDimensionalMultiIndexDerivative α f x‖

/-- Least-upper-bound presentation of the printed full Wightman Schwartz control `|f|_{n,w}`. -/
structure OSIIWightmanPrintedSchwartzControlData (n order : ℕ) where
  /-- Exact control value for every full Wightman Schwartz test. -/
  control : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n → ℝ
  control_nonnegative : ∀ f, 0 ≤ control f
  /-- Every exact weighted derivative term with `|α| ≤ order` is bounded. -/
  weightedDerivative_le : ∀
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n),
    fourDimensionalMultiIndexOrder α ≤ order → ∀ x,
      osIIWightmanWeightedDerivativeTerm order α f x ≤ control f
  /-- The control is the least common upper bound of those exact terms. -/
  control_le_of_weightedDerivative_le : ∀
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n) (bound : ℝ),
    (∀ (α : FourDimensionalMultiIndex n),
      fourDimensionalMultiIndexOrder α ≤ order → ∀ x,
        osIIWightmanWeightedDerivativeTerm order α f x ≤ bound) →
    control f ≤ bound

namespace OSIIWightmanPrintedSchwartzControlData

/-- The universal property uniquely determines the printed Wightman control. -/
theorem control_unique
    {n order : ℕ} (first second : OSIIWightmanPrintedSchwartzControlData n order) :
    first.control = second.control := by
  funext f
  apply le_antisymm
  · exact first.control_le_of_weightedDerivative_le f (second.control f)
      (second.weightedDerivative_le f)
  · exact second.control_le_of_weightedDerivative_le f (first.control f)
      (first.weightedDerivative_le f)

/-- A strictly positive exact term prevents a fake zero control. -/
theorem control_ne_zero_of_term_pos
    {n order : ℕ} (data : OSIIWightmanPrintedSchwartzControlData n order)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n)
    (α : FourDimensionalMultiIndex n)
    (order_le : fourDimensionalMultiIndexOrder α ≤ order)
    (x : Mathematics.FiniteConfiguration (Spacetime EuclideanDimension.four) n)
    (term_pos : 0 < osIIWightmanWeightedDerivativeTerm order α f x) :
    data.control f ≠ 0 := by
  intro control_zero
  have bound := data.weightedDerivative_le f α order_le x
  rw [control_zero] at bound
  exact (not_lt_of_ge bound) term_pos

end OSIIWightmanPrintedSchwartzControlData

/-- The positive coefficient sequence and exact `α β^(n²)` bound in OS-II `(R0′)`.

The source says only “for some constants `α, β`”; no extra sign assumptions are inserted. Positivity
of every coefficient plus the bound forces each corresponding right-hand side to be positive. -/
structure OSIIWightmanLinearGrowthCoefficientData where
  coefficient : PositiveArity → ℝ
  coefficient_pos : ∀ n, 0 < coefficient n
  alpha : ℝ
  beta : ℝ
  coefficient_bound : ∀ n,
    coefficient n ≤ alpha * beta ^ (n.value ^ 2)

/-- OS-II `(R0′)` on the exact existing four-dimensional full Wightman distributions. -/
structure OSIIWightmanLinearGrowthData
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData EuclideanDimension.four G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {fieldData : ScalarWightmanFieldOnCommonDomainData D}
    (full : ScalarWightmanJointTemperedCorrelatorData fieldData) where
  /-- One common positive Schwartz order `w` for every positive arity. -/
  order : ℕ
  order_positive : 0 < order
  growth : OSIIWightmanLinearGrowthCoefficientData
  printedControl : ∀ n : PositiveArity,
    OSIIWightmanPrintedSchwartzControlData n.value order
  /-- Equation (4.3) on the exact full `n`-point Wightman distribution. -/
  bound : ∀ (n : PositiveArity)
    (f : ScalarMinkowskiNPointSchwartzTestFunction EuclideanDimension.four n.value),
    ‖full.nPointDistribution n.value f‖ ≤
      growth.coefficient n * (printedControl n).control f

/-- The source coefficient hypotheses force every selected `α β^(n²)` bound to be positive. -/
theorem OSIIWightmanLinearGrowthCoefficientData.bound_positive
    (growth : OSIIWightmanLinearGrowthCoefficientData) (n : PositiveArity) :
    0 < growth.alpha * growth.beta ^ (n.value ^ 2) :=
  lt_of_lt_of_le (growth.coefficient_pos n) (growth.coefficient_bound n)

end

end YangMills.Minkowski
