/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Dimensions.TwoDimensionalLatticeSpacingActionFamily
import YangMills.Geometry.InvariantInnerProduct

/-!
# Driver's representation differential and induced Lie-algebra pairing

Driver §2 fixes a representation `p`, defines `p_*` as its derivative, assumes `p_*` injective, and
uses the real pairing `(X,Y)_p = -Re tr(p_*X p_*Y)` to define the Casimir and heat semigroup. This
module records that exact common-representation chain. It does not construct such a representation,
inner product, heat kernel, or convergence theorem.
-/

namespace YangMills.Dimensions

open YangMills.Mathematics
open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G]
    [T2Space G] [SecondCountableTopology G] [ChartedSpace E G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G]

/-- One actual smooth unitary matrix representation with Driver's injective differential `p_*`. -/
structure SmoothUnitaryRepresentationDifferentialData extends
    FiniteDimensionalUnitaryRepresentationCharacterData G where
  representation_contMDiff : ContMDiff (modelWithCornersSelf ℝ E)
    (modelWithCornersSelf ℝ
      (Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension →
        Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension → ℂ)) ∞
    (fun g i j => toFiniteDimensionalUnitaryRepresentationCharacterData.representation g i j)
  differential_injective : Function.Injective
    (mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ
        (Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension →
          Fin toFiniteDimensionalUnitaryRepresentationCharacterData.dimension → ℂ))
      (fun g i j => toFiniteDimensionalUnitaryRepresentationCharacterData.representation g i j)
      (1 : G))

namespace SmoothUnitaryRepresentationDifferentialData

/-- Driver's `p_*`, definitionally the manifold derivative of the same matrix representation at the
group identity. -/
def differential (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    GroupLieAlgebra (modelWithCornersSelf ℝ E) G →L[ℝ]
      (Fin data.dimension → Fin data.dimension → ℂ) :=
  mfderiv (modelWithCornersSelf ℝ E)
    (modelWithCornersSelf ℝ (Fin data.dimension → Fin data.dimension → ℂ))
    (fun g i j => data.representation g i j) (1 : G)

omit [FiniteDimensional ℝ E] [T2Space G] [SecondCountableTopology G]
    [LieGroup (modelWithCornersSelf ℝ E) ∞ G] in
/-- The stored source hypothesis is injectivity of this exact derivative. -/
theorem differential_injective_exact
    (data : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G)) :
    Function.Injective data.differential :=
  data.differential_injective

end SmoothUnitaryRepresentationDifferentialData

/-- Exact real trace pairing induced by the same representation differential. -/
def twoDimensionalRepresentationTracePairing
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (first second : GroupLieAlgebra (modelWithCornersSelf ℝ E) G) : ℝ :=
  -(Matrix.trace (representation.differential first * representation.differential second)).re

/-- The continuum invariant inner product is exactly Driver's representation-induced trace pairing,
not an independently chosen normalization. -/
structure TwoDimensionalRepresentationInducedPairingCoherenceData
    (representation : SmoothUnitaryRepresentationDifferentialData (E := E) (G := G))
    (inner : Geometry.InvariantInnerProductData
      (I := modelWithCornersSelf ℝ E) (G := G)) : Prop where
  pairing_eq_trace : ∀ first second,
    inner.pairing first second =
      twoDimensionalRepresentationTracePairing representation first second

end

end YangMills.Dimensions
