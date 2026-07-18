/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.WightmanField
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Scalar Wightman locality

Streater–Wightman, printed p. 100, axiom `III`, requires fields (and fields with adjoints) to
(anti)commute when their test supports are spacelike separated. For the scalar bosonic interface,
this module chooses commutation and defines separation using topological supports and the exact
mostly-minus Minkowski quadratic form.

The separation domain is proved nonvacuous in every spacetime dimension at least two: continuity of
the Minkowski form supplies disjoint neighborhoods around an explicit spacelike pair, and Mathlib's
finite-dimensional bump theorem supplies nonzero Schwartz tests supported in those neighborhoods.
Dimension one is not given a fake spacelike pair.

No local field datum, Wightman theory, spectrum, reconstruction, existence theorem, or mass gap is
constructed.
-/

namespace YangMills.Minkowski

/-- Open set of ordered spacelike-separated Minkowski point pairs. -/
def spacelikeSeparatedPointPairSet (d : EuclideanDimension) :
    Set (Spacetime d × Spacetime d) :=
  {p | d.minkowskiQuadraticForm (p.1 - p.2) < 0}

/-- The Minkowski quadratic form is continuous on the finite-dimensional coordinate carrier. -/
theorem continuous_minkowskiQuadraticForm (d : EuclideanDimension) :
    Continuous d.minkowskiQuadraticForm := by
  change Continuous (fun p : Spacetime d => d.minkowskiQuadraticForm p)
  simp only [EuclideanDimension.minkowskiQuadraticForm,
    QuadraticMap.weightedSumSquares_apply]
  apply continuous_finsetSum Finset.univ
  intro i _
  fun_prop

/-- Spacelike separation is an open relation. -/
theorem isOpen_spacelikeSeparatedPointPairSet (d : EuclideanDimension) :
    IsOpen (spacelikeSeparatedPointPairSet d) := by
  apply isOpen_lt
  · exact (continuous_minkowskiQuadraticForm d).comp (by fun_prop)
  · fun_prop

/-- In one-dimensional spacetime there are no spacelike-separated point pairs. -/
theorem oneDimensional_spacelikeSeparatedPointPairSet_eq_empty :
    spacelikeSeparatedPointPairSet EuclideanDimension.one = ∅ := by
  ext p
  constructor
  · intro hspace
    change EuclideanDimension.one.minkowskiQuadraticForm (p.1 - p.2) < 0 at hspace
    rw [← EuclideanDimension.one_euclideanQuadraticForm_eq_minkowskiQuadraticForm] at hspace
    exact (not_lt_of_ge
      (EuclideanDimension.one.euclideanQuadraticForm_nonneg (p.1 - p.2))) hspace
  · simp

/-- Two scalar Minkowski Schwartz tests have spacelike-separated topological supports. -/
def HaveSpacelikeSeparatedTopologicalSupports
    {d : EuclideanDimension}
    (f g : ScalarMinkowskiSchwartzTestFunction d) : Prop :=
  ∀ x ∈ tsupport f, ∀ y ∈ tsupport g,
    d.minkowskiQuadraticForm (x - y) < 0

/-- Dimension one cannot hide vacuity behind empty support once both tests are nonzero. -/
theorem oneDimensional_no_nonzero_spacelikeSeparated_schwartzTests
    {f g : ScalarMinkowskiSchwartzTestFunction EuclideanDimension.one}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ¬ HaveSpacelikeSeparatedTopologicalSupports f g := by
  intro hsep
  have hfx : ∃ x, f x ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext x
    exact hn x
  have hgy : ∃ y, g y ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hg
    ext y
    exact hn y
  rcases hfx with ⟨x, hx⟩
  rcases hgy with ⟨y, hy⟩
  have hxSupport : x ∈ tsupport f := subset_tsupport f hx
  have hySupport : y ∈ tsupport g := subset_tsupport g hy
  have hnegative := hsep x hxSupport y hySupport
  rw [← EuclideanDimension.one_euclideanQuadraticForm_eq_minkowskiQuadraticForm] at hnegative
  exact (not_lt_of_ge
    (EuclideanDimension.one.euclideanQuadraticForm_nonneg (x - y))) hnegative

/-- Spacelike support separation is symmetric. -/
theorem haveSpacelikeSeparatedTopologicalSupports_comm
    {d : EuclideanDimension}
    {f g : ScalarMinkowskiSchwartzTestFunction d}
    (h : HaveSpacelikeSeparatedTopologicalSupports f g) :
    HaveSpacelikeSeparatedTopologicalSupports g f := by
  intro y hy x hx
  have hxy := h x hx y hy
  have hneg : y - x = -(x - y) := by abel
  rw [hneg, QuadraticMap.map_neg]
  exact hxy

/-- In every dimension with a spatial coordinate, there are two nonzero Schwartz tests with
spacelike-separated topological supports. -/
theorem exists_nonzero_spacelikeSeparated_scalarMinkowskiSchwartzTests
    (d : EuclideanDimension) (h : 2 ≤ d.value) :
    ∃ f g : ScalarMinkowskiSchwartzTestFunction d,
      f ≠ 0 ∧ g ≠ 0 ∧ HaveSpacelikeSeparatedTopologicalSupports f g := by
  let i : Fin d.spatialDimension :=
    ⟨0, by simp [EuclideanDimension.spatialDimension]; omega⟩
  let x0 : Spacetime d := d.basisVector (d.spatialIndexSucc i)
  let y0 : Spacetime d := -x0
  have hcenter : (x0, y0) ∈ spacelikeSeparatedPointPairSet d := by
    change d.minkowskiQuadraticForm (x0 - y0) < 0
    dsimp [y0]
    rw [sub_neg_eq_add, ← two_smul ℝ, QuadraticMap.map_smul]
    simp [x0]
  have hnhds := (isOpen_spacelikeSeparatedPointPairSet d).mem_nhds hcenter
  rcases mem_nhds_prod_iff'.mp hnhds with
    ⟨u, v, huOpen, hx0u, hvOpen, hy0v, huv⟩
  rcases exists_contDiff_tsupport_subset (n := ⊤) (huOpen.mem_nhds hx0u) with
    ⟨rf, hrfSupport, hrfCompact, hrfSmooth, _, hrfOne⟩
  rcases exists_contDiff_tsupport_subset (n := ⊤) (hvOpen.mem_nhds hy0v) with
    ⟨rg, hrgSupport, hrgCompact, hrgSmooth, _, hrgOne⟩
  let f : ScalarMinkowskiSchwartzTestFunction d :=
    (hrfCompact.comp_left rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hrfSmooth)
  let g : ScalarMinkowskiSchwartzTestFunction d :=
    (hrgCompact.comp_left rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hrgSmooth)
  refine ⟨f, g, ?_, ?_, ?_⟩
  · intro hf
    have atCenter := congrArg
      (fun q : ScalarMinkowskiSchwartzTestFunction d => q x0) hf
    change Complex.ofRealCLM (rf x0) = 0 at atCenter
    rw [hrfOne] at atCenter
    norm_num at atCenter
  · intro hg
    have atCenter := congrArg
      (fun q : ScalarMinkowskiSchwartzTestFunction d => q y0) hg
    change Complex.ofRealCLM (rg y0) = 0 at atCenter
    rw [hrgOne] at atCenter
    norm_num at atCenter
  · intro x hx y hy
    change (x, y) ∈ spacelikeSeparatedPointPairSet d
    apply huv
    constructor
    · apply hrfSupport
      change x ∈ tsupport (Complex.ofRealCLM ∘ rf) at hx
      exact (tsupport_comp_subset rfl rf) hx
    · apply hrgSupport
      change y ∈ tsupport (Complex.ofRealCLM ∘ rg) at hy
      exact (tsupport_comp_subset rfl rg) hy

/-- Scalar bosonic locality for field and adjoint on the exact common domain. -/
structure ScalarWightmanLocalityData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (fieldData : ScalarWightmanFieldOnCommonDomainData D) : Prop where
  /-- Field-field commutation at spacelike-separated supports. -/
  field_field : ∀ f g, HaveSpacelikeSeparatedTopologicalSupports f g → ∀ ψ,
    fieldData.field f (fieldData.field g ψ) =
      fieldData.field g (fieldData.field f ψ)
  /-- Field-adjoint commutation. -/
  field_adjoint : ∀ f g, HaveSpacelikeSeparatedTopologicalSupports f g → ∀ ψ,
    fieldData.field f (fieldData.adjointField g ψ) =
      fieldData.adjointField g (fieldData.field f ψ)
  /-- Adjoint-field commutation. -/
  adjoint_field : ∀ f g, HaveSpacelikeSeparatedTopologicalSupports f g → ∀ ψ,
    fieldData.adjointField f (fieldData.field g ψ) =
      fieldData.field g (fieldData.adjointField f ψ)
  /-- Adjoint-adjoint commutation. -/
  adjoint_adjoint : ∀ f g, HaveSpacelikeSeparatedTopologicalSupports f g → ∀ ψ,
    fieldData.adjointField f (fieldData.adjointField g ψ) =
      fieldData.adjointField g (fieldData.adjointField f ψ)

end YangMills.Minkowski
