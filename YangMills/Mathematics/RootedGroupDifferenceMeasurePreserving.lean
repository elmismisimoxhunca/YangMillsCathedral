/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Mathematics.RootedGroupDifference
import Mathlib.MeasureTheory.Group.Prod

/-!
# Haar preservation of rooted group differences

The upper and lower rooted noncommutative difference equivalences preserve every finite product of
a common sigma-finite bi-invariant, inversion-invariant measure. The proof splits off the final
coordinate, applies a measurable skew product by a Haar translation (and inversion for the upper
orientation), and inducts on chain length.

This is reusable measure-theoretic group infrastructure. It constructs no Yang--Mills measure.
-/

namespace YangMills.Mathematics.RootedGroupDifference

open MeasureTheory
noncomputable section

set_option linter.unusedSectionVars false

universe uG
variable {G : Type uG} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  [Measure.IsInvInvariant μ]

abbrev rootedProductMeasure (n : ℕ) : Measure (Fin n → G) :=
  Measure.pi fun _ : Fin n => μ

private theorem splitLast_measurePreserving (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) (Fin.last n))
      (rootedProductMeasure μ (n + 1)) (μ.prod (rootedProductMeasure μ n)) := by
  simpa [rootedProductMeasure] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n))

private theorem unsplitLast_measurePreserving (n : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) (Fin.last n)).symm
      (μ.prod (rootedProductMeasure μ n)) (rootedProductMeasure μ (n + 1)) :=
  MeasurePreserving.symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => G) (Fin.last n))
    (splitLast_measurePreserving μ n)

private theorem swapLast_measurePreserving (n : ℕ) :
    MeasurePreserving Prod.swap (μ.prod (rootedProductMeasure μ n))
      ((rootedProductMeasure μ n).prod μ) :=
  Measure.measurePreserving_swap

private theorem unswapLast_measurePreserving (n : ℕ) :
    MeasurePreserving Prod.swap ((rootedProductMeasure μ n).prod μ)
      (μ.prod (rootedProductMeasure μ n)) :=
  Measure.measurePreserving_swap

private theorem lowerSkewLast_measurePreserving (n : ℕ)
    (prefixMP : MeasurePreserving (lowerForward : (Fin (n + 1) → G) → _)
      (rootedProductMeasure μ (n + 1)) (rootedProductMeasure μ (n + 1))) :
    MeasurePreserving
      (fun p : (Fin (n + 1) → G) × G =>
        (lowerForward p.1, (p.1 (Fin.last n))⁻¹ * p.2))
      ((rootedProductMeasure μ (n + 1)).prod μ) ((rootedProductMeasure μ (n + 1)).prod μ) := by
  refine prefixMP.skew_product
    (g := fun pre value => (pre (Fin.last n))⁻¹ * value) ?_ ?_
  · fun_prop
  · exact Filter.Eventually.of_forall fun pre =>
      (measurePreserving_mul_left μ (pre (Fin.last n))⁻¹).map_eq

private theorem upperSkewLast_measurePreserving (n : ℕ)
    (prefixMP : MeasurePreserving (upperForward : (Fin (n + 1) → G) → _)
      (rootedProductMeasure μ (n + 1)) (rootedProductMeasure μ (n + 1))) :
    MeasurePreserving
      (fun p : (Fin (n + 1) → G) × G =>
        (upperForward p.1, p.2⁻¹ * p.1 (Fin.last n)))
      ((rootedProductMeasure μ (n + 1)).prod μ) ((rootedProductMeasure μ (n + 1)).prod μ) := by
  refine prefixMP.skew_product
    (g := fun pre value => value⁻¹ * pre (Fin.last n)) ?_ ?_
  · fun_prop
  · exact Filter.Eventually.of_forall fun pre =>
      ((measurePreserving_mul_right μ (pre (Fin.last n))).comp
        (Measure.measurePreserving_inv μ)).map_eq

private theorem lowerForward_init {n : ℕ} (values : Fin (n + 1) → G) :
    lowerForward (Fin.init values) = Fin.init (lowerForward values) := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change values 0 = values 0
        rfl
      · simp [Fin.init]

private theorem upperForward_init {n : ℕ} (values : Fin (n + 1) → G) :
    upperForward (Fin.init values) = Fin.init (upperForward values) := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (values 0)⁻¹ = (values 0)⁻¹
        rfl
      · simp [Fin.init]

private theorem lowerForward_eq_splitComposition (n : ℕ) :
    (lowerForward : (Fin (n + 2) → G) → (Fin (n + 2) → G)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => G) (Fin.last (n + 1))).symm ∘
      Prod.swap ∘
      (fun p : (Fin (n + 1) → G) × G =>
        (lowerForward p.1, (p.1 (Fin.last n))⁻¹ * p.2)) ∘
      Prod.swap ∘
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => G) (Fin.last (n + 1))) := by
  funext values index
  refine Fin.lastCases ?_ (fun i => ?_) index
  · simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl, lowerForward_succ]
    rfl
  · simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rw [lowerForward_init]
    rfl

private theorem upperForward_eq_splitComposition (n : ℕ) :
    (upperForward : (Fin (n + 2) → G) → (Fin (n + 2) → G)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => G) (Fin.last (n + 1))).symm ∘
      Prod.swap ∘
      (fun p : (Fin (n + 1) → G) × G =>
        (upperForward p.1, p.2⁻¹ * p.1 (Fin.last n))) ∘
      Prod.swap ∘
      (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 2) => G) (Fin.last (n + 1))) := by
  funext values index
  refine Fin.lastCases ?_ (fun i => ?_) index
  · simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rw [show Fin.last (n + 1) = (Fin.last n).succ by rfl, upperForward_succ]
    rfl
  · simp [Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rw [upperForward_init]
    rfl

/-- Lower rooted differences preserve every finite product under the common bi-invariant,
inversion-invariant hypotheses used by both orientations. The proof itself uses left invariance. -/
theorem lowerForward_measurePreserving {n : ℕ} :
    MeasurePreserving (lowerForward : (Fin n → G) → (Fin n → G))
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) := by
  induction n with
  | zero =>
      rw [show (lowerForward : (Fin 0 → G) → _) = id by
        funext values i
        exact Fin.elim0 i]
      exact MeasurePreserving.id (rootedProductMeasure μ 0)
  | succ n ih =>
      cases n with
      | zero =>
          rw [show (lowerForward : (Fin 1 → G) → _) = id by
            funext values i
            exact Fin.cases (by simp) (fun j => Fin.elim0 j) i]
          exact MeasurePreserving.id (rootedProductMeasure μ 1)
      | succ n =>
          rw [lowerForward_eq_splitComposition (G := G) n]
          exact (unsplitLast_measurePreserving μ (n + 1)).comp
            ((unswapLast_measurePreserving μ (n + 1)).comp
              ((lowerSkewLast_measurePreserving μ n ih).comp
                ((swapLast_measurePreserving μ (n + 1)).comp
                  (splitLast_measurePreserving μ (n + 1)))))

/-- Upper rooted differences preserve every finite product of a bi-invariant inversion-invariant
measure. -/
theorem upperForward_measurePreserving {n : ℕ} :
    MeasurePreserving (upperForward : (Fin n → G) → (Fin n → G))
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) := by
  induction n with
  | zero =>
      rw [show (upperForward : (Fin 0 → G) → _) = id by
        funext values i
        exact Fin.elim0 i]
      exact MeasurePreserving.id (rootedProductMeasure μ 0)
  | succ n ih =>
      cases n with
      | zero =>
          rw [show (upperForward : (Fin 1 → G) → _) = Inv.inv by
            funext values i
            exact Fin.cases (by simp) (fun j => Fin.elim0 j) i]
          exact Measure.measurePreserving_inv (rootedProductMeasure μ 1)
      | succ n =>
          rw [upperForward_eq_splitComposition (G := G) n]
          exact (unsplitLast_measurePreserving μ (n + 1)).comp
            ((unswapLast_measurePreserving μ (n + 1)).comp
              ((upperSkewLast_measurePreserving μ n ih).comp
                ((swapLast_measurePreserving μ (n + 1)).comp
                  (splitLast_measurePreserving μ (n + 1)))))

/-- The packaged lower measurable equivalence preserves the same finite product measure. -/
theorem lowerMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (lowerMeasurableEquiv (G := G) n)
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  lowerForward_measurePreserving μ

/-- Its recursively defined inverse preserves the same finite product measure. -/
theorem lowerRecover_measurePreserving (n : ℕ) :
    MeasurePreserving (lowerMeasurableEquiv (G := G) n).symm
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  MeasurePreserving.symm (lowerMeasurableEquiv (G := G) n)
    (lowerMeasurableEquiv_measurePreserving μ n)

/-- The packaged upper measurable equivalence preserves the same finite product measure. -/
theorem upperMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (upperMeasurableEquiv (G := G) n)
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  upperForward_measurePreserving μ

/-- Its recursively defined inverse preserves the same finite product measure. -/
theorem upperRecover_measurePreserving (n : ℕ) :
    MeasurePreserving (upperMeasurableEquiv (G := G) n).symm
      (rootedProductMeasure μ n) (rootedProductMeasure μ n) :=
  MeasurePreserving.symm (upperMeasurableEquiv (G := G) n)
    (upperMeasurableEquiv_measurePreserving μ n)

end
end YangMills.Mathematics.RootedGroupDifference
