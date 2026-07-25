/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.Vacuum
import YangMills.Minkowski.QuadraticTopology
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Joint spectral data for physical translations

Streater–Wightman, printed p. 92, invokes the SNAG theorem and writes the translation
representation as one momentum-space projection-valued measure `E`: intersection corresponds to
projection multiplication, disjoint Borel unions to strong sums, and `E(ℝ⁴) = 1`. Printed p. 97
requires its support to lie in the closed forward cone. This module packages those semantics for the
same translation representation already selected by the physical Poincaré representation.

Because Mathlib currently has no bundled projection-valued-measure/SNAG API, the reusable PVM
interface below states strong countable additivity directly and supplies finite diagonal spectral
measures. Their Fourier formula ties the PVM to the exact physical translation unitaries; it is not a
disconnected energy surrogate. No PVM, representation, quantum theory, mass gap, or existence
witness is constructed.
-/

namespace YangMills.Minkowski

open MeasureTheory

/-- The mostly-minus pairing between momentum and a spacetime translation. -/
def minkowskiMomentumPairing (d : EuclideanDimension)
    (p a : Spacetime d) : ℝ :=
  ∑ i, d.minkowskiWeight i * p i * a i

/-- The unit-modulus character occurring in the SNAG translation formula. -/
noncomputable def minkowskiTranslationCharacter (d : EuclideanDimension)
    (p a : Spacetime d) : ℂ :=
  Complex.exp (Complex.I * minkowskiMomentumPairing d p a)

/-- The momentum character is continuous as a function of momentum. -/
theorem continuous_minkowskiTranslationCharacter
    (d : EuclideanDimension) (a : Spacetime d) :
    Continuous (fun p => minkowskiTranslationCharacter d p a) := by
  unfold minkowskiTranslationCharacter minkowskiMomentumPairing
  apply Complex.continuous_exp.comp
  apply Continuous.mul continuous_const
  apply Complex.continuous_ofReal.comp
  apply continuous_finsetSum Finset.univ
  intro i _
  fun_prop

/-- A normalized projection-valued measure with strong countable additivity.

The projection is defined on every set so expressions involving spectral complements are literal;
all algebraic and additivity laws require Borel measurability. -/
structure ProjectionValuedMeasureData
    (X H : Type*) [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Borel set projection. -/
  projection : Set X → H →L[ℂ] H
  /-- Every measurable-set value is idempotent. -/
  projection_idempotent : ∀ s, MeasurableSet s → projection s * projection s = projection s
  /-- Every measurable-set value is self-adjoint. -/
  projection_selfAdjoint : ∀ s, MeasurableSet s →
    (projection s).adjoint = projection s
  /-- Empty-set normalization. -/
  projection_empty : projection ∅ = 0
  /-- Whole-space normalization. -/
  projection_univ : projection Set.univ = 1
  /-- Multiplication of measurable projections is intersection. -/
  projection_mul : ∀ s t, MeasurableSet s → MeasurableSet t →
    projection s * projection t = projection (s ∩ t)
  /-- Countable additivity for pairwise-disjoint measurable sets in the strong operator topology. -/
  projection_iUnion_strongly : ∀ s : ℕ → Set X,
    (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) →
    ∀ ψ : H,
      Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, projection (s n) ψ)
        Filter.atTop (nhds (projection (⋃ n, s n) ψ))

/-- A measurable spectral subset of a zero-projection set also has zero projection. -/
theorem ProjectionValuedMeasureData.projection_eq_zero_of_subset
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : ProjectionValuedMeasureData X H)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : s ⊆ t) (htZero : E.projection t = 0) :
    E.projection s = 0 := by
  have hinter : s ∩ t = s := Set.inter_eq_left.mpr hst
  calc
    E.projection s = E.projection (s ∩ t) := by rw [hinter]
    _ = E.projection s * E.projection t := (E.projection_mul s t hs ht).symm
    _ = 0 := by rw [htZero, mul_zero]

/-- Lorentz transport of a momentum-space set by the projected Poincaré transformation. The
translation component does not act on momentum. -/
def lorentzMomentumImage
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (lift : ProperOrthochronousPoincareLiftData d G)
    (g : G) (s : Set (Spacetime d)) : Set (Spacetime d) :=
  (lift.projection g).lorentz.linear '' s

/-- One physical joint momentum PVM tied to the exact translation representation by the diagonal
matrix-element form of the SNAG Fourier formula. -/
structure JointTranslationSpectralData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation lift H) where
  /-- The single joint PVM on physical momentum space. -/
  pvm : ProjectionValuedMeasureData (Spacetime d) H
  /-- Positive diagonal scalar measures induced by that PVM. -/
  diagonalMeasure : H → Measure (Spacetime d)
  /-- Exact measurable-set coherence between diagonal measures and PVM projections. -/
  diagonalMeasure_apply : ∀ ψ s, MeasurableSet s →
    diagonalMeasure ψ s =
      ENNReal.ofReal (Complex.re (inner ℂ ψ (pvm.projection s ψ)))
  /-- Exact SNAG Fourier formula for the same physical translation unitaries. -/
  translation_fourier_diagonal : ∀ a ψ,
    inner ℂ ψ (U.translationUnitary a ψ) =
      ∫ p, minkowskiTranslationCharacter d p a ∂ diagonalMeasure ψ
  /-- The same full Poincaré representation transports the PVM by the projected Lorentz action. -/
  poincare_covariant : ∀ g s, MeasurableSet s →
    U.unitary g * pvm.projection s * U.unitary (g⁻¹) =
      pvm.projection (lorentzMomentumImage lift g s)

/-- Each diagonal spectral measure has finite total mass. -/
theorem JointTranslationSpectralData.diagonalMeasure_univ_lt_top
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (spectrum : JointTranslationSpectralData U) (ψ : H) :
    spectrum.diagonalMeasure ψ Set.univ < ⊤ := by
  rw [spectrum.diagonalMeasure_apply ψ Set.univ MeasurableSet.univ,
    spectrum.pvm.projection_univ]
  exact ENNReal.ofReal_lt_top

/-- The character in the SNAG formula is genuinely integrable against every diagonal spectral
measure; the integral therefore cannot collapse via Mathlib's nonintegrable-zero convention. -/
theorem JointTranslationSpectralData.integrable_translationCharacter
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (spectrum : JointTranslationSpectralData U) (a : Spacetime d) (ψ : H) :
    Integrable (fun p => minkowskiTranslationCharacter d p a)
      (spectrum.diagonalMeasure ψ) := by
  letI : IsFiniteMeasure (spectrum.diagonalMeasure ψ) :=
    ⟨spectrum.diagonalMeasure_univ_lt_top ψ⟩
  apply Integrable.of_bound
    (continuous_minkowskiTranslationCharacter d a).aestronglyMeasurable 1
  filter_upwards with p
  rw [minkowskiTranslationCharacter, Complex.norm_exp]
  simp

/-- Closed future cone in mostly-minus momentum coordinates. -/
def closedForwardMomentumCone (d : EuclideanDimension) : Set (Spacetime d) :=
  {p | 0 ≤ p d.timeIndex ∧ 0 ≤ d.minkowskiQuadraticForm p}

/-- The closed future momentum cone is Borel measurable. -/
theorem isClosed_closedForwardMomentumCone (d : EuclideanDimension) :
    IsClosed (closedForwardMomentumCone d) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const (continuous_apply d.timeIndex)
  · exact isClosed_le continuous_const (continuous_minkowskiQuadraticForm d)

/-- Joint spectral data satisfying the Wightman forward-cone spectrum condition. -/
structure ForwardConeJointTranslationSpectrumData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (U : StronglyContinuousUnitaryPoincareRepresentation lift H) where
  /-- The PVM and exact SNAG tie to the physical translations. -/
  joint : JointTranslationSpectralData U
  /-- The closed forward cone carries the full spectral projection. -/
  forward_cone_full :
    joint.pvm.projection (closedForwardMomentumCone d) = 1
  /-- No spectral projection lies outside the closed forward cone. -/
  outside_forward_cone_zero :
    joint.pvm.projection (closedForwardMomentumCone d)ᶜ = 0

/-- The Hamiltonian spectral projection is the energy-coordinate pushforward of the same physical
joint PVM, restricted to its full forward-cone support. -/
def physicalHamiltonianSpectralProjection
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (spectrum : ForwardConeJointTranslationSpectrumData U)
    (s : Set ℝ) : H →L[ℂ] H :=
  spectrum.joint.pvm.projection
    (closedForwardMomentumCone d ∩ (fun p : Spacetime d => p d.timeIndex) ⁻¹' s)

/-- The derived Hamiltonian spectral view is normalized. -/
theorem physicalHamiltonianSpectralProjection_univ
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (spectrum : ForwardConeJointTranslationSpectrumData U) :
    physicalHamiltonianSpectralProjection spectrum Set.univ = 1 := by
  simpa [physicalHamiltonianSpectralProjection] using spectrum.forward_cone_full

/-- The nonzero future subgap momentum region, excluding the vacuum momentum itself. -/
def nonzeroFutureSubgapMomentumRegion (d : EuclideanDimension) (Δ : ℝ) : Set (Spacetime d) :=
  {p | p ∈ closedForwardMomentumCone d ∧ p ≠ 0 ∧
    d.minkowskiQuadraticForm p < Δ ^ 2}

/-- The nonzero future subgap momentum region is Borel measurable. -/
theorem measurableSet_nonzeroFutureSubgapMomentumRegion
    (d : EuclideanDimension) (Δ : ℝ) :
    MeasurableSet (nonzeroFutureSubgapMomentumRegion d Δ) := by
  have hset : nonzeroFutureSubgapMomentumRegion d Δ =
      (closedForwardMomentumCone d ∩ ({0} : Set (Spacetime d))ᶜ) ∩
        {p | d.minkowskiQuadraticForm p < Δ ^ 2} := by
    ext p
    constructor
    · rintro ⟨hcone, hnonzero, hmass⟩
      exact ⟨⟨hcone, hnonzero⟩, hmass⟩
    · rintro ⟨⟨hcone, hnonzero⟩, hmass⟩
      exact ⟨hcone, hnonzero, hmass⟩
  rw [hset]
  exact ((isClosed_closedForwardMomentumCone d).measurableSet.inter
    (measurableSet_singleton (0 : Spacetime d)).compl).inter
      (isOpen_lt (continuous_minkowskiQuadraticForm d)
        (continuous_const : Continuous (fun _ : Spacetime d => Δ ^ 2))).measurableSet

/-- The strictly positive energy interval below a proposed Clay Hamiltonian gap. -/
def positiveEnergySubgapRegion (d : EuclideanDimension) (Δ : ℝ) : Set (Spacetime d) :=
  {p | p ∈ closedForwardMomentumCone d ∧
    0 < p d.timeIndex ∧ p d.timeIndex < Δ}

/-- The positive-energy subgap region is Borel measurable. -/
theorem measurableSet_positiveEnergySubgapRegion
    (d : EuclideanDimension) (Δ : ℝ) :
    MeasurableSet (positiveEnergySubgapRegion d Δ) := by
  exact (isClosed_closedForwardMomentumCone d).measurableSet.inter
    ((isOpen_lt continuous_const (continuous_apply d.timeIndex)).measurableSet.inter
      (isOpen_lt (continuous_apply d.timeIndex)
        (continuous_const : Continuous (fun _ : Spacetime d => Δ))).measurableSet)

/-- Nonzero future momenta in a bounded positive-energy band. -/
def boundedPositiveEnergyExcitationRegion
    (d : EuclideanDimension) (E : ℝ) : Set (Spacetime d) :=
  {p | p ∈ closedForwardMomentumCone d ∧
    0 < p d.timeIndex ∧ p d.timeIndex ≤ E}

/-- A bounded positive-energy excitation band is Borel measurable. -/
theorem measurableSet_boundedPositiveEnergyExcitationRegion
    (d : EuclideanDimension) (E : ℝ) :
    MeasurableSet (boundedPositiveEnergyExcitationRegion d E) := by
  exact (isClosed_closedForwardMomentumCone d).measurableSet.inter
    ((isOpen_lt continuous_const (continuous_apply d.timeIndex)).measurableSet.inter
      (isClosed_le (continuous_apply d.timeIndex)
        (continuous_const : Continuous (fun _ : Spacetime d => E))).measurableSet)

/-- Nonzero future spectral momenta with invariant mass bounded by a finite scale. -/
def finiteMassExcitationRegion (d : EuclideanDimension) (M : ℝ) : Set (Spacetime d) :=
  {p | p ∈ closedForwardMomentumCone d ∧ p ≠ 0 ∧
    d.minkowskiQuadraticForm p ≤ M ^ 2}

/-- The finite-mass excitation region is Borel measurable. -/
theorem measurableSet_finiteMassExcitationRegion
    (d : EuclideanDimension) (M : ℝ) :
    MeasurableSet (finiteMassExcitationRegion d M) := by
  have hset : finiteMassExcitationRegion d M =
      (closedForwardMomentumCone d ∩ ({0} : Set (Spacetime d))ᶜ) ∩
        {p | d.minkowskiQuadraticForm p ≤ M ^ 2} := by
    ext p
    constructor
    · rintro ⟨hcone, hnonzero, hmass⟩
      exact ⟨⟨hcone, hnonzero⟩, hmass⟩
    · rintro ⟨⟨hcone, hnonzero⟩, hmass⟩
      exact ⟨hcone, hnonzero, hmass⟩
  rw [hset]
  exact ((isClosed_closedForwardMomentumCone d).measurableSet.inter
    (measurableSet_singleton (0 : Spacetime d)).compl).inter
      (isClosed_le (continuous_minkowskiQuadraticForm d)
        (continuous_const : Continuous (fun _ : Spacetime d => M ^ 2))).measurableSet

/-- Physical joint-spectral mass-gap semantics for a selected positive threshold.

The zero-momentum projection is exactly the normalized vacuum line in the same Hilbert space, and
the same physical joint PVM vanishes on every nonzero future momentum whose invariant mass squared
is below `Δ²`. A nonzero projection in a bounded positive-energy band above the gap excludes the
vacuum-only spectrum and implements Clay's finite Hamiltonian-gap/nontrivial-excitation guard. This
is a predicate only; no `Δ`, finite scale, or satisfying theory is produced. -/
def HasPhysicalJointSpectralMassGap
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (vacuumData : PoincareInvariantVacuumData U)
    (spectrum : ForwardConeJointTranslationSpectrumData U)
    (Δ : ℝ) : Prop :=
  0 < Δ ∧
  (∀ ψ : H, spectrum.joint.pvm.projection ({0} : Set (Spacetime d)) ψ =
    inner ℂ vacuumData.vacuum ψ • vacuumData.vacuum) ∧
  spectrum.joint.pvm.projection (nonzeroFutureSubgapMomentumRegion d Δ) = 0 ∧
  ∃ E : ℝ, 0 < E ∧ Δ ≤ E ∧
    spectrum.joint.pvm.projection (boundedPositiveEnergyExcitationRegion d E) ≠ 0

/-- Every measurable set disjoint from the closed forward cone has zero physical spectral
projection. -/
theorem ForwardConeJointTranslationSpectrumData.projection_eq_zero_of_disjoint_forwardCone
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    (spectrum : ForwardConeJointTranslationSpectrumData U)
    {s : Set (Spacetime d)} (hs : MeasurableSet s)
    (houtside : s ⊆ (closedForwardMomentumCone d)ᶜ) :
    spectrum.joint.pvm.projection s = 0 :=
  spectrum.joint.pvm.projection_eq_zero_of_subset hs
    (isClosed_closedForwardMomentumCone d).measurableSet.compl houtside
    spectrum.outside_forward_cone_zero

/-- The invariant-mass predicate implies Clay's Hamiltonian statement: the same PVM vanishes on
all strictly positive energies below `Δ`. -/
theorem HasPhysicalJointSpectralMassGap.positiveEnergySubgap_projection_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection (positiveEnergySubgapRegion d Δ) = 0 := by
  apply spectrum.joint.pvm.projection_eq_zero_of_subset
    (measurableSet_positiveEnergySubgapRegion d Δ)
    (measurableSet_nonzeroFutureSubgapMomentumRegion d Δ)
  · intro p hp
    have hpNonzero : p ≠ 0 := by
      intro hpZero
      subst p
      simpa using hp.2.1
    have hmassLe := minkowskiQuadraticForm_le_timeSquare d p
    exact ⟨hp.1, hpNonzero, by nlinarith [hgap.1, hp.2.1, hp.2.2]⟩
  · exact hgap.2.2.1

/-- Clay's Hamiltonian interval `(0, Δ)` has zero projection in the exact energy-coordinate
pushforward of the physical joint PVM. -/
theorem HasPhysicalJointSpectralMassGap.hamiltonian_Ioo_projection_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    physicalHamiltonianSpectralProjection spectrum (Set.Ioo 0 Δ) = 0 := by
  have hset : closedForwardMomentumCone d ∩
      (fun p : Spacetime d => p d.timeIndex) ⁻¹' Set.Ioo 0 Δ =
      positiveEnergySubgapRegion d Δ := by
    ext p
    rfl
  rw [physicalHamiltonianSpectralProjection, hset]
  exact hgap.positiveEnergySubgap_projection_zero

/-- The gap predicate contains a nonzero bounded positive-energy projection in the same derived
Hamiltonian spectral view. -/
theorem HasPhysicalJointSpectralMassGap.exists_boundedHamiltonian_excitation
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    ∃ E : ℝ, 0 < E ∧ Δ ≤ E ∧
      physicalHamiltonianSpectralProjection spectrum (Set.Ioc 0 E) ≠ 0 := by
  rcases hgap.2.2.2 with ⟨E, hE, hΔE, hExcitation⟩
  refine ⟨E, hE, hΔE, ?_⟩
  have hset : closedForwardMomentumCone d ∩
      (fun p : Spacetime d => p d.timeIndex) ⁻¹' Set.Ioc 0 E =
      boundedPositiveEnergyExcitationRegion d E := by
    ext p
    rfl
  simpa [physicalHamiltonianSpectralProjection, hset] using hExcitation

/-- The required bounded positive-energy excitation also supplies a finite invariant-mass scale. -/
theorem HasPhysicalJointSpectralMassGap.exists_finiteMass_scale
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    ∃ M : ℝ, 0 < M ∧ Δ ≤ M ∧
      spectrum.joint.pvm.projection (finiteMassExcitationRegion d M) ≠ 0 := by
  rcases hgap.2.2.2 with ⟨E, hE, hΔE, hExcitation⟩
  refine ⟨E, hE, hΔE, ?_⟩
  intro hFiniteMassZero
  apply hExcitation
  apply spectrum.joint.pvm.projection_eq_zero_of_subset
    (measurableSet_boundedPositiveEnergyExcitationRegion d E)
    (measurableSet_finiteMassExcitationRegion d E)
  · intro p hp
    have hpNonzero : p ≠ 0 := by
      intro hpZero
      subst p
      simpa using hp.2.1
    have hmassLe := minkowskiQuadraticForm_le_timeSquare d p
    exact ⟨hp.1, hpNonzero, by nlinarith [hp.2.1, hp.2.2]⟩
  · exact hFiniteMassZero

/-- A physical mass gap has a genuine nonvacuum spectral sector; the vacuum-only PVM is rejected. -/
theorem HasPhysicalJointSpectralMassGap.nonvacuum_projection_ne_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ) :
    spectrum.joint.pvm.projection (({0} : Set (Spacetime d))ᶜ) ≠ 0 := by
  rcases hgap.2.2.2 with ⟨E, _, _, hExcitation⟩
  intro hVacuumOnly
  apply hExcitation
  apply spectrum.joint.pvm.projection_eq_zero_of_subset
    (measurableSet_boundedPositiveEnergyExcitationRegion d E)
    (measurableSet_singleton (0 : Spacetime d)).compl
  · intro p hp hpZero
    subst p
    simpa using hp.2.1
  · exact hVacuumOnly

/-- A physical mass gap annihilates the singleton projection at every nonzero future momentum below
its invariant-mass threshold. -/
theorem HasPhysicalJointSpectralMassGap.singleton_projection_zero
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {spectrum : ForwardConeJointTranslationSpectrumData U}
    {Δ : ℝ} (hgap : HasPhysicalJointSpectralMassGap vacuumData spectrum Δ)
    {p : Spacetime d} (hfuture : p ∈ closedForwardMomentumCone d)
    (hp : p ≠ 0) (hmass : d.minkowskiQuadraticForm p < Δ ^ 2) :
    spectrum.joint.pvm.projection ({p} : Set (Spacetime d)) = 0 := by
  apply spectrum.joint.pvm.projection_eq_zero_of_subset
    (measurableSet_singleton p)
    (measurableSet_nonzeroFutureSubgapMomentumRegion d Δ)
  · intro q hq
    have hqp : q = p := by simpa using hq
    subst q
    exact ⟨hfuture, hp, hmass⟩
  · exact hgap.2.2.1

end YangMills.Minkowski
