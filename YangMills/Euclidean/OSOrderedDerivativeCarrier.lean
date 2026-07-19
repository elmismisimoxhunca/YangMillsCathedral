/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Euclidean.SchwingerOrderedTestSpace

/-!
# Osterwalder–Schrader ordered Fréchet candidate carrier

Osterwalder–Schrader I, printed p. 86, defines the closed subspace
`S_{s,t}(ℝ^{4n})` by requiring every partial derivative to vanish unless
`s < x₁⁰ < ... < xₙ⁰ < t`, and sets `S₊ = S_{0,∞}`. This module models only a
project-dimension **Fréchet candidate for `S₊`**, using vanishing of every iterated real Fréchet
derivative outside the strict positive ordered region. It is intended as a coordinate-free
strengthening at this layer. Downstream modules complete the four-dimensional multi-index,
permutation and `D^α` comparison at every positive arity, prove this internal candidate closed, and
transport closedness to the exact positive-arity source spaces. The natural-arity-zero extension in
this foundational carrier is not identified with OS-I's separately declared scalar component.

Unlike the earlier strict-support carrier, this definition does not require topological support to
be contained in the open ordered set: boundary points may remain in topological support while all
jets vanish there. The topology is exactly the subtype/induced topology from Mathlib Schwartz space.
No direct-sum topology, completed positive-half-space tensor product, `(E2)`, reconstruction, or
inhabitant of an OS theory is asserted. In particular, OS-II printed p. 282 reports the failure of
OS-I Lemma 8.8 and leaves sufficiency of the original axioms open; OS-II printed p. 287 introduces
the strengthened linear-growth hypothesis. This candidate supplies neither correction and cannot
serve as a reconstruction theorem.
-/

namespace YangMills

open Set Filter Topology

noncomputable section

/-- Every iterated Fréchet derivative vanishes outside the exact strict-positive ordered region. -/
def IsOSPositiveTimeOrderedDerivativeVanishing
    {d : EuclideanDimension} {n : ℕ} (f : ScalarSchwartzTestFunction d n) : Prop :=
  ∀ k : ℕ, ∀ x : EuclideanNPointSpace d n,
    x ∉ strictPositiveTimeOrderedConfigurationSet d n →
      iteratedFDeriv ℝ k (f : EuclideanNPointSpace d n → ℂ) x = 0

/-- The candidate condition is a complex-linear subspace of the exact ambient Schwartz carrier. -/
def osPositiveTimeOrderedDerivativeSubmodule
    (d : EuclideanDimension) (n : ℕ) :
    Submodule ℂ (ScalarSchwartzTestFunction d n) where
  carrier := {f | IsOSPositiveTimeOrderedDerivativeVanishing f}
  zero_mem' := by
    intro k x hx
    change iteratedFDeriv ℝ k
      (0 : EuclideanNPointSpace d n → ℂ) x = 0
    rw [iteratedFDeriv_zero]
    rfl
  add_mem' := by
    intro f g hf hg k x hx
    change iteratedFDeriv ℝ k
      ((f : EuclideanNPointSpace d n → ℂ) +
        (g : EuclideanNPointSpace d n → ℂ)) x = 0
    rw [iteratedFDeriv_add_apply (f.smooth k).contDiffAt (g.smooth k).contDiffAt,
      hf k x hx, hg k x hx, add_zero]
  smul_mem' := by
    intro scalar f hf k x hx
    change iteratedFDeriv ℝ k
      (scalar • (f : EuclideanNPointSpace d n → ℂ)) x = 0
    rw [iteratedFDeriv_const_smul_apply (f.smooth k).contDiffAt, hf k x hx, smul_zero]

/-- Project-dimension Fréchet candidate underlying the OS ordered space. Downstream modules prove
its coordinate equivalence and closedness and, at four-dimensional positive arities, identify it
with exact formal `D^α` source membership. Its generic dimension and natural-arity-zero instances
remain project infrastructure rather than source-facing OS-I spaces. Its membership predicate is
exactly the carrier of the named complex submodule above. -/
def OSPositiveTimeOrderedDerivativeCarrier
    (d : EuclideanDimension) (n : ℕ) :=
  {f : ScalarSchwartzTestFunction d n // IsOSPositiveTimeOrderedDerivativeVanishing f}

namespace OSPositiveTimeOrderedDerivativeCarrier

variable {d : EuclideanDimension} {n : ℕ}

/-- Exact algebraic identification with the named complex Schwartz submodule. -/
def equivSubmodule :
    OSPositiveTimeOrderedDerivativeCarrier d n ≃
      osPositiveTimeOrderedDerivativeSubmodule d n where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f.1, f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Candidate membership is exactly membership in the named complex submodule. -/
@[simp]
theorem mem_submodule_iff (f : ScalarSchwartzTestFunction d n) :
    f ∈ osPositiveTimeOrderedDerivativeSubmodule d n ↔
      IsOSPositiveTimeOrderedDerivativeVanishing f :=
  Iff.rfl

/-- Forgetful map to the exact ambient Mathlib Schwartz carrier. -/
def toSchwartz (f : OSPositiveTimeOrderedDerivativeCarrier d n) :
    ScalarSchwartzTestFunction d n :=
  f.1

instance : Coe (OSPositiveTimeOrderedDerivativeCarrier d n)
    (ScalarSchwartzTestFunction d n) :=
  ⟨toSchwartz⟩

/-- Named induced topology from the exact ambient Schwartz topology. -/
instance : TopologicalSpace (OSPositiveTimeOrderedDerivativeCarrier d n) :=
  TopologicalSpace.induced toSchwartz inferInstance

/-- The carrier topology is exactly induced from the ambient Schwartz topology. -/
theorem inducing_toSchwartz :
    IsInducing (toSchwartz : OSPositiveTimeOrderedDerivativeCarrier d n →
      ScalarSchwartzTestFunction d n) :=
  Topology.IsInducing.induced toSchwartz

/-- The forgetful map is injective, hence a topological embedding for the induced topology. -/
theorem embedding_toSchwartz :
    IsEmbedding (toSchwartz : OSPositiveTimeOrderedDerivativeCarrier d n →
      ScalarSchwartzTestFunction d n) :=
  ⟨inducing_toSchwartz, Subtype.val_injective⟩

/-- Exact law of the declared Fréchet candidate predicate; source equivalence is not claimed. -/
theorem derivative_vanishes_outside
    (f : OSPositiveTimeOrderedDerivativeCarrier d n)
    (k : ℕ) (x : EuclideanNPointSpace d n)
    (hx : x ∉ strictPositiveTimeOrderedConfigurationSet d n) :
    iteratedFDeriv ℝ k
      ((toSchwartz f : ScalarSchwartzTestFunction d n) :
        EuclideanNPointSpace d n → ℂ) x = 0 :=
  f.2 k x hx

/-- Any strict topological-support test includes into the broader derivative-vanishing candidate. -/
def ofStrictOrderedFlat
    (f : MathlibPositiveTimeOrderedFlatTestFunction d n) :
    OSPositiveTimeOrderedDerivativeCarrier d n := by
  refine ⟨f.toSchwartz, ?_⟩
  intro k x hx
  have hnotSupport : x ∉ tsupport
      (f.toSchwartz : EuclideanNPointSpace d n → ℂ) := by
    intro hsupport
    exact hx (f.ordered_support hsupport)
  have hnhds : (tsupport
      (f.toSchwartz : EuclideanNPointSpace d n → ℂ))ᶜ ∈ nhds x :=
    (isClosed_tsupport
      (f.toSchwartz : EuclideanNPointSpace d n → ℂ)).isOpen_compl.mem_nhds hnotSupport
  have hevent :
      (f.toSchwartz : EuclideanNPointSpace d n → ℂ) =ᶠ[nhds x] 0 := by
    filter_upwards [hnhds] with y hy
    by_contra hne
    exact hy (subset_tsupport _ (Function.mem_support.mpr hne))
  have hderiv := Filter.EventuallyEq.iteratedFDeriv ℝ hevent k
  simpa using hderiv.eq_of_nhds

/-- The explicit positive-time bump supplies a genuine nonzero arity-one carrier element. -/
def positiveTimeBump (d : EuclideanDimension) :
    OSPositiveTimeOrderedDerivativeCarrier d 1 :=
  ofStrictOrderedFlat (positiveTimeBumpOrderedFlatTest d)

/-- The explicit arity-one carrier element is not the zero Schwartz test. -/
theorem positiveTimeBump_toSchwartz_ne_zero (d : EuclideanDimension) :
    toSchwartz (positiveTimeBump d) ≠ 0 :=
  positiveTimeBumpSchwartz_ne_zero d

end OSPositiveTimeOrderedDerivativeCarrier

end

end YangMills
