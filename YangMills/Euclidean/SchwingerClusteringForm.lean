/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerReflectionPositivityForm
import YangMills.Euclidean.SchwingerSpatialRay

/-!
# Algebraic scalar Schwinger clustering form

OS-I `(E4)` requires the connected correlation between `Θ f*` and a copy of `g` translated along a
spatial ray to tend to zero. This module wires the exact finite-sequence expression

`S((Θ f*) × T_{scale a} g) - S(Θ f*) S(g)`

and packages convergence along one explicitly supplied unit spatial direction.

The predicate is deliberately parameterized by a direction. Dimension one has no such direction,
so this avoids silently declaring a universally quantified direction condition vacuous there. It is
also named `MathlibStrict...`, not OS-I `(E4)`: the strict-support/source-space and topology
comparisons remain unproved. No Schwinger family satisfying clustering is constructed.
-/

namespace YangMills

/-- The exact unrestricted reflected-star sequence associated to a strict positive-time input. -/
noncomputable def mathlibStrictReflectedStarSequence
    {d : EuclideanDimension} (f : MathlibStrictPositiveTimeTestSequence d) :
    ScalarFiniteSchwartzSequence d :=
  finiteSchwartzSequenceReflectedStar d f.toFiniteSchwartzSequence

/-- The exact unrestricted sequence obtained by translating a strict input along a supplied spatial
ray. -/
noncomputable def mathlibStrictSpatialRayTranslatedSequence
    {d : EuclideanDimension} (v : EuclideanUnitSpatialDirection d) (scale : ℝ)
    (g : MathlibStrictPositiveTimeTestSequence d) : ScalarFiniteSchwartzSequence d :=
  translateScalarFiniteSchwartzSequenceAlongSpatialRay d v scale g.toFiniteSchwartzSequence

/-- The connected finite-sequence clustering expression at one real ray scale.

The first term preserves the source order `(Θ f*) × translated(g)`. The subtraction term is the
product of the separately evaluated reflected and untranslated clusters. -/
noncomputable def mathlibStrictScalarClusteringExpression
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (v : EuclideanUnitSpatialDirection d)
    (f g : MathlibStrictPositiveTimeTestSequence d) (scale : ℝ) : ℂ :=
  finiteSequenceSchwingerEvaluation family
      (finiteSchwartzSequenceConvolution d
        (mathlibStrictReflectedStarSequence f)
        (mathlibStrictSpatialRayTranslatedSequence v scale g)) -
    finiteSequenceSchwingerEvaluation family (mathlibStrictReflectedStarSequence f) *
      finiteSequenceSchwingerEvaluation family g.toFiniteSchwartzSequence

/-- Scalar clustering along one explicitly supplied unit spatial direction on the current strict
Mathlib positive-time domain.

This is a strict-subdomain candidate predicate, not source-facing `(E4)`. -/
def MathlibStrictScalarClusteringAlongDirection
    {d : EuclideanDimension} (family : ScalarSchwingerDistributionFamily d)
    (v : EuclideanUnitSpatialDirection d) : Prop :=
  ∀ f g : MathlibStrictPositiveTimeTestSequence d,
    Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family v f g scale)
      Filter.atTop (nhds 0)

/-- The candidate predicate exposes the exact clustering limit for every pair of strict inputs. -/
theorem MathlibStrictScalarClusteringAlongDirection.apply
    {d : EuclideanDimension} {family : ScalarSchwingerDistributionFamily d}
    {v : EuclideanUnitSpatialDirection d}
    (h : MathlibStrictScalarClusteringAlongDirection family v)
    (f g : MathlibStrictPositiveTimeTestSequence d) :
    Filter.Tendsto (fun scale : ℝ =>
      mathlibStrictScalarClusteringExpression family v f g scale)
      Filter.atTop (nhds 0) :=
  h f g

end YangMills
