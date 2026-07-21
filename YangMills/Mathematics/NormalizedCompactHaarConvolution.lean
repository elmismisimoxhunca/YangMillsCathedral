/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.NormalizedCompactHaarMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Density convolution against normalized compact Haar measure

This module fixes the multiplicative convolution convention

`(f ⋆ g)(z) = ∫⁻ x, f(x) g(x⁻¹ z) dμ_H(x)`

against the exact probability-normalized compact Haar measure. The orientation matches the kernel
`Q_t(h⁻¹g)` in Driver and the displayed convolution in Sengupta. Equivalent formulas using central
or inversion-symmetric functions require separate proofs and are not substituted definitionally.

No convolution semigroup, continuity, density, or heat kernel is constructed.
-/

namespace YangMills.Mathematics

open MeasureTheory

/-- Multiplicative `ENNReal` density convolution against canonical normalized compact Haar. -/
noncomputable def normalizedCompactHaarDensityConvolution
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f g : G → ENNReal) (z : G) : ENNReal :=
  ∫⁻ x, f x * g (x⁻¹ * z) ∂normalizedCompactHaarMeasure G

/-- The exact source-facing convolution orientation is exposed without simplification. -/
theorem normalizedCompactHaarDensityConvolution_apply
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (f g : G → ENNReal) (z : G) :
    normalizedCompactHaarDensityConvolution G f g z =
      ∫⁻ x, f x * g (x⁻¹ * z) ∂normalizedCompactHaarMeasure G :=
  rfl

end YangMills.Mathematics
