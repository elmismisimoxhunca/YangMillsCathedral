/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Lattice.FiniteProductHaarGibbsMeasure

/-!
# Hostile probes for finite product Haar and Gibbs data

These probes expose nonempty link indexing, exact normalized Haar marginals, both-sided and inversion
invariance, exact product/reference identity, and derived—not disconnected—Gibbs normalization.
No compact gauge-group certificate, potential measurability datum, or Gibbs theory is constructed.
-/

namespace YangMills.Lattice.FiniteProductHaarMeasure.Probes

open MeasureTheory

variable
    {d : EuclideanDimension} {Λ : FinitePeriodicLattice}
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {potential : PlaquettePotentialData G} {coupling : LatticeCouplingData}

/-- The product is not an empty-index artifact: every allowed dimension has an explicit link. -/
def explicitPositiveLink : PositiveOrientedLink d Λ where
  base := fun _ => ⟨0, by simp [FinitePeriodicLattice.extent]⟩
  direction := ⟨0, d.one_le⟩

/-- Normalized Haar is a genuine probability measure and hence cannot be zero. -/
theorem zero_normalized_haar_blocked : normalizedCompactHaarMeasure G ≠ 0 := by
  letI : IsProbabilityMeasure (normalizedCompactHaarMeasure G) :=
    normalizedCompactHaarMeasure_isProbability G
  exact IsProbabilityMeasure.ne_zero _

/-- Left invariance uses the exact normalized Haar measure. -/
theorem exact_left_haar_invariance (g : G) :
    Measure.map (g * ·) (normalizedCompactHaarMeasure G) =
      normalizedCompactHaarMeasure G :=
  normalizedCompactHaarMeasure_map_mul_left G g

/-- Compact Haar uniqueness supplies exact right invariance. -/
theorem exact_right_haar_invariance (g : G) :
    Measure.map (· * g) (normalizedCompactHaarMeasure G) =
      normalizedCompactHaarMeasure G :=
  normalizedCompactHaarMeasure_map_mul_right G g

/-- Compact normalized Haar is exactly inversion-invariant. -/
theorem exact_inversion_haar_invariance :
    Measure.map Inv.inv (normalizedCompactHaarMeasure G) =
      normalizedCompactHaarMeasure G := by
  rw [← Measure.inv_def]
  exact (normalizedCompactHaarMeasure_isInvInvariant G).inv_eq_self

/-- The explicit link marginal is exactly normalized Haar, not merely some invariant measure. -/
theorem explicit_link_marginal :
    Measure.map (Function.eval (explicitPositiveLink (d := d) (Λ := Λ)))
      (finiteGaugeFieldProductHaarMeasure Λ G) = normalizedCompactHaarMeasure G :=
  finiteGaugeFieldProductHaarMeasure_map_eval Λ G explicitPositiveLink

/-- The exact finite product reference is nonzero. -/
theorem zero_product_reference_blocked :
    finiteGaugeFieldProductHaarMeasure (d := d) Λ G ≠ 0 := by
  intro hzero
  have h := finiteGaugeFieldProductHaarMeasure_probability (d := d) Λ G
  rw [hzero] at h
  simp at h

/-- Local gauge transformations preserve the exact product, coordinate by coordinate. -/
theorem exact_product_gauge_invariance (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g) (finiteGaugeFieldProductHaarMeasure Λ G) =
      finiteGaugeFieldProductHaarMeasure Λ G :=
  finiteGaugeFieldProductHaarMeasure_gaugeInvariant Λ G g

/-- Conversion to the generic Gibbs checker fixes the reference definitionally to product Haar. -/
theorem exact_specialized_reference
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    data.toFiniteLatticeGibbsMeasureData.referenceMeasure =
      finiteGaugeFieldProductHaarMeasure Λ G :=
  rfl

/-- An unrelated reference measure cannot pass through the specialized conversion. -/
theorem unrelated_reference_blocked
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (μ : Measure (GaugeField d Λ G))
    (hunrelated : μ ≠ finiteGaugeFieldProductHaarMeasure Λ G) :
    data.toFiniteLatticeGibbsMeasureData.referenceMeasure ≠ μ := by
  rw [exact_specialized_reference data]
  exact hunrelated.symm

/-- Partition positivity is derived from product-Haar probability and the exact positive density. -/
theorem exact_specialized_partition_positive
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    0 < finiteProductHaarLatticePartitionFunction (d := d) (Λ := Λ) G
      potential coupling :=
  data.partition_pos

/-- Partition finiteness is derived from the action bound by one. -/
theorem exact_specialized_partition_finite
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    finiteProductHaarLatticePartitionFunction (d := d) (Λ := Λ) G
      potential coupling ≠ ⊤ :=
  data.partition_ne_top

/-- Gibbs probability normalization is a theorem on the same product-Haar chain. -/
theorem exact_specialized_gibbs_probability
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling) :
    normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
      potential coupling Set.univ = 1 :=
  data.gibbs_probability

/-- Gibbs gauge invariance is derived from exact product and density invariance. -/
theorem exact_specialized_gibbs_gauge_invariance
    (data : @FiniteProductHaarGibbsMeasureData d Λ G _ _ _ _ _ _ potential coupling)
    (g : GaugeTransformation d Λ G) :
    Measure.map (gaugeTransform g)
      (normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling) =
      normalizedFiniteProductHaarLatticeGibbsMeasure (d := d) (Λ := Λ) G
        potential coupling :=
  data.gibbs_gaugeInvariant g

end YangMills.Lattice.FiniteProductHaarMeasure.Probes
