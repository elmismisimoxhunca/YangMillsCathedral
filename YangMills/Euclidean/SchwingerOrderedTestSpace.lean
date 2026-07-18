/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.PositiveTimeSchwartzBump

/-!
# Time-ordered and coincidence-flat Schwinger test infrastructure

Osterwalder–Schrader I, printed pp. 86–88, uses a closed Schwartz subspace whose partial
derivatives vanish on point-coincidence diagonals and ordered spaces whose derivatives vanish unless
the selected Euclidean times lie in a strict interval and order. This module defines a deliberately
stronger Mathlib subspace: the topological support itself lies in the strict positive time-ordered
region, and every iterated Fréchet derivative vanishes at every coincident configuration.

The record is deliberately named `MathlibPositiveTimeOrderedFlatTestFunction`. It is not claimed
equivalent to OS-I's carrier: boundary-flat source functions may have boundary points in their
topological support and therefore lie outside this strict subspace. A future bridge must establish
the precise embedding, sufficiency, density, or completion relation and compare full Fréchet
flatness with OS-I's multi-index condition. It must separately track the induced topology on each
ordered arity space, the direct-sum topology on finite-support sequences, and OS-I's distinct
completed tensor-product construction for positive-half-space tests. No finite test-sequence
product or reflection positivity `(E2)` is asserted here.
-/

namespace YangMills

/-- A configuration has a point coincidence when two distinct point labels carry the same
Euclidean spacetime point. -/
def HasPointCoincidence
    {d : EuclideanDimension} {n : ℕ} (x : EuclideanNPointSpace d n) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ x i = x j

/-- Every iterated real Fréchet derivative of a scalar Schwartz test vanishes at every point
coincidence. -/
def IsFlatAtPointCoincidences
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) : Prop :=
  ∀ k : ℕ, ∀ x : EuclideanNPointSpace d n,
    HasPointCoincidence x →
      iteratedFDeriv ℝ k (f : EuclideanNPointSpace d n → ℂ) x = 0

/-- Configurations with strictly positive selected times, strictly increasing in point-label order. -/
def strictPositiveTimeOrderedConfigurationSet
    (d : EuclideanDimension) (n : ℕ) : Set (EuclideanNPointSpace d n) :=
  {x | (∀ i, 0 < x i (euclideanTimeCoordinate d)) ∧
    ∀ i j, i < j →
      x i (euclideanTimeCoordinate d) < x j (euclideanTimeCoordinate d)}

/-- Topological support lies in the strict-positive, strictly time-ordered configuration set. -/
def HasStrictPositiveTimeOrderedSupport
    (d : EuclideanDimension) {n : ℕ} (f : ScalarSchwartzTestFunction d n) : Prop :=
  tsupport f ⊆ strictPositiveTimeOrderedConfigurationSet d n

/-- Strict ordered topological-support containment already forces infinite-order flatness at point
coincidences.

This theorem records the redundancy inside the present strict subspace. The flatness field remains
named below because it is independent in OS-I's broader derivative-vanishing carrier. -/
theorem strictOrderedSupport_implies_coincidenceFlat
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n)
    (hsupport : HasStrictPositiveTimeOrderedSupport d f) :
    IsFlatAtPointCoincidences f := by
  intro k x hcoin
  rcases hcoin with ⟨i, j, hne, heq⟩
  have hnotOrdered : x ∉ strictPositiveTimeOrderedConfigurationSet d n := by
    intro hordered
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hlt := hordered.2 i j hij
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    · have hlt := hordered.2 j i hji
      rw [heq] at hlt
      exact lt_irrefl _ hlt
  have hnotSupport : x ∉ tsupport (f : EuclideanNPointSpace d n → ℂ) := by
    intro hx
    exact hnotOrdered (hsupport hx)
  have hnhds : (tsupport (f : EuclideanNPointSpace d n → ℂ))ᶜ ∈ nhds x :=
    (isClosed_tsupport (f : EuclideanNPointSpace d n → ℂ)).isOpen_compl.mem_nhds hnotSupport
  have hevent : (f : EuclideanNPointSpace d n → ℂ) =ᶠ[nhds x] 0 := by
    filter_upwards [hnhds] with y hy
    by_contra hnezero
    have hmem : y ∈ Function.support (f : EuclideanNPointSpace d n → ℂ) :=
      Function.mem_support.mpr hnezero
    exact hy (subset_tsupport (f : EuclideanNPointSpace d n → ℂ) hmem)
  have hderiv := Filter.EventuallyEq.iteratedFDeriv ℝ hevent k
  simpa using hderiv.eq_of_nhds

/-- A concrete strict Mathlib subspace associated with one arity of OS-I's positive-time ordered,
diagonal-flat test space. Topological-support containment makes it stronger than the printed
all-derivatives-vanish-outside condition. -/
structure MathlibPositiveTimeOrderedFlatTestFunction
    (d : EuclideanDimension) (n : ℕ) where
  /-- The underlying exact scalar Schwartz test. -/
  toSchwartz : ScalarSchwartzTestFunction d n
  /-- Strict positive-time ordering of its topological support. -/
  ordered_support : HasStrictPositiveTimeOrderedSupport d toSchwartz
  /-- Infinite-order Fréchet flatness on all point-coincidence diagonals.

  For this strict support subspace the property is logically redundant by
  `strictOrderedSupport_implies_coincidenceFlat`, but it remains an explicit field because it is
  independent in OS-I's broader derivative-vanishing carrier and must survive the future comparison
  bridge. -/
  coincidence_flat : IsFlatAtPointCoincidences toSchwartz

/-- At arity one, the explicit positive-time bump satisfies ordering and coincidence-flatness
vacuously beyond its already proved strict-positive support. -/
noncomputable def positiveTimeBumpOrderedFlatTest (d : EuclideanDimension) :
    MathlibPositiveTimeOrderedFlatTestFunction d 1 where
  toSchwartz := positiveTimeBumpSchwartz d
  ordered_support := by
    intro x hx
    constructor
    · exact positiveTimeBumpSchwartz_hasStrictPositiveTimeSupport d hx
    · intro i j hij
      omega
  coincidence_flat := by
    intro k x hcoin
    rcases hcoin with ⟨i, j, hne, _⟩
    exact (hne (Subsingleton.elim i j)).elim

end YangMills
