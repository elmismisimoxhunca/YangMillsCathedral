/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import YangMills.Mathematics.UnitaryMatrixDualAlgebraicPlancherel

/-!
# The normalized-Haar `L²` coefficient span

This file maps the algebraic finite-support coefficient synthesis into Mathlib's actual
`Lp ℂ 2 μ_H` carrier. The `L²` inner product of two synthesized vectors is proved equal to the
previously derived dimension-weighted algebraic Fourier pairing.

The algebraic image and its topological closure are then defined inside `L²`. The proposition
`UnitaryMatrixDual.HasL2PeterWeylCompleteness G` is exactly the statement that this closed span is
the whole `L²` space, equivalently that the algebraic image is dense.

No inhabitant of that completeness proposition is constructed here. Thus the carrier, inner-product
bridge, closure, and exact Peter–Weyl target are available without assuming density or infinite
Fourier convergence.
-/

namespace YangMills
namespace Mathematics

open MeasureTheory

noncomputable section

universe uG

/-- Complex `L²` for probability-normalized Haar measure. -/
abbrev NormalizedCompactHaarL2
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] := Lp ℂ 2 (normalizedCompactHaarMeasure G)

/-- Algebraic coefficient synthesis bundled into the continuous-function carrier. -/
def unitaryMatrixDualContinuousCoefficientSynthesis
 (G:Type uG) [Group G] [TopologicalSpace G] :
 UnitaryMatrixDualCoefficientSpace G →ₗ[ℂ] C(G,ℂ) where
 toFun A := ⟨unitaryMatrixDualCoefficientSynthesis G A,
  continuous_unitaryMatrixDualCoefficientSynthesis A⟩
 map_add' A B := by
  ext g
  exact congrFun (map_add (unitaryMatrixDualCoefficientSynthesis G) A B) g
 map_smul' c A := by
  ext g
  exact congrFun (map_smul (unitaryMatrixDualCoefficientSynthesis G) c A) g

/-- The exact linear map from finite-support dual coefficients into normalized-Haar `L²`. -/
def unitaryMatrixDualL2CoefficientSynthesis
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 UnitaryMatrixDualCoefficientSpace G →ₗ[ℂ] NormalizedCompactHaarL2 G := by
 letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
  normalizedCompactHaarMeasure_isProbability G
 exact (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ).toLinearMap.comp
  (unitaryMatrixDualContinuousCoefficientSynthesis G)

/-- The actual `L²` inner product equals the all-coordinate-class algebraic Fourier pairing. -/
theorem unitaryMatrixDualL2CoefficientSynthesis_inner
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
 (A B:UnitaryMatrixDualCoefficientSpace G) :
 inner ℂ (unitaryMatrixDualL2CoefficientSynthesis G A)
  (unitaryMatrixDualL2CoefficientSynthesis G B) =
 unitaryMatrixDualAlgebraicFourierPairing A B := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  rw [←unitaryMatrixDualAlgebraicCoefficientSynthesis_fourier_plancherel A B]
  change inner ℂ
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ
      (unitaryMatrixDualContinuousCoefficientSynthesis G A))
    (ContinuousMap.toLp 2 (normalizedCompactHaarMeasure G) ℂ
      (unitaryMatrixDualContinuousCoefficientSynthesis G B)) = _
  rw [ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with g
  change unitaryMatrixDualCoefficientSynthesis G B g *
    star (unitaryMatrixDualCoefficientSynthesis G A g) = _
  ring

/-- The algebraic finite-support coefficient image inside `L²`. -/
def unitaryMatrixDualL2AlgebraicRange
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 Submodule ℂ (NormalizedCompactHaarL2 G) :=
 LinearMap.range (unitaryMatrixDualL2CoefficientSynthesis G)

/-- The closed `L²` span of all algebraically synthesized coordinate-dual coefficients. -/
def unitaryMatrixDualL2CoefficientClosedSpan
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 Submodule ℂ (NormalizedCompactHaarL2 G) :=
 (unitaryMatrixDualL2AlgebraicRange G).topologicalClosure

/-- Exact `L²` Peter–Weyl completeness target for the coordinate unitary dual. -/
def UnitaryMatrixDual.HasL2PeterWeylCompleteness
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] : Prop :=
 unitaryMatrixDualL2CoefficientClosedSpan G = ⊤

theorem unitaryMatrixDual_hasL2PeterWeylCompleteness_iff_dense
 {G:Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 UnitaryMatrixDual.HasL2PeterWeylCompleteness G ↔
 Dense (unitaryMatrixDualL2AlgebraicRange G :
  Set (NormalizedCompactHaarL2 G)) := by
 unfold UnitaryMatrixDual.HasL2PeterWeylCompleteness
 unfold unitaryMatrixDualL2CoefficientClosedSpan
 exact Submodule.dense_iff_topologicalClosure_eq_top.symm

theorem unitaryMatrixDualL2AlgebraicRange_le_closedSpan
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 unitaryMatrixDualL2AlgebraicRange G ≤
 unitaryMatrixDualL2CoefficientClosedSpan G :=
 Submodule.le_topologicalClosure _

theorem unitaryMatrixDualL2CoefficientClosedSpan_isClosed
 (G:Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 [MeasurableSpace G] [BorelSpace G] [CompactSpace G] :
 IsClosed (unitaryMatrixDualL2CoefficientClosedSpan G :
  Set (NormalizedCompactHaarL2 G)) :=
 by
  unfold unitaryMatrixDualL2CoefficientClosedSpan
  exact Submodule.isClosed_topologicalClosure _

end

end Mathematics
end YangMills
