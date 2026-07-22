/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Rooted noncommutative difference coordinates

Ordered difference coordinates on a finite chain rooted at the group identity. Upper-oriented
differences use `D₀ = U₀⁻¹` and `Dᵢ₊₁ = Uᵢ₊₁⁻¹Uᵢ`; lower-oriented differences use
`D₀ = U₀` and `Dᵢ₊₁ = Uᵢ⁻¹Uᵢ₊₁`. Explicit recursive recovery proves both are exact measurable
equivalences without assuming commutativity.

This is general finite-chain group and measurable-space infrastructure. It constructs no measure or
Yang--Mills object.
-/

namespace YangMills.Mathematics.RootedGroupDifference

universe uG

variable {G : Type uG} [Group G]

/-- Upper-oriented rooted differences:
`D₀ = U₀⁻¹` and `Dᵢ₊₁ = Uᵢ₊₁⁻¹ Uᵢ`. -/
def upperForward : ∀ {n : ℕ}, (Fin n → G) → (Fin n → G)
  | 0, _ => fun i => Fin.elim0 i
  | _ + 1, values => Fin.cons (values 0)⁻¹
      (fun i => (values i.succ)⁻¹ * values i.castSucc)

/-- Explicit recursive recovery from upper-oriented rooted differences:
`U₀ = D₀⁻¹` and `Uᵢ₊₁ = Uᵢ Dᵢ₊₁⁻¹`. -/
def upperRecover : ∀ {n : ℕ}, (Fin n → G) → (Fin n → G)
  | 0, _ => fun i => Fin.elim0 i
  | _ + 1, differences => fun i =>
      Fin.induction (differences 0)⁻¹
        (fun j previous => previous * (differences j.succ)⁻¹) i

@[simp]
theorem upperForward_zero {n : ℕ} (values : Fin (n + 1) → G) :
    upperForward values 0 = (values 0)⁻¹ := by
  simp [upperForward]

@[simp]
theorem upperForward_succ {n : ℕ} (values : Fin (n + 1) → G) (i : Fin n) :
    upperForward values i.succ = (values i.succ)⁻¹ * values i.castSucc := by
  simp [upperForward]

@[simp]
theorem upperRecover_zero {n : ℕ} (differences : Fin (n + 1) → G) :
    upperRecover differences 0 = (differences 0)⁻¹ := by
  simp [upperRecover]

@[simp]
theorem upperRecover_succ {n : ℕ} (differences : Fin (n + 1) → G) (i : Fin n) :
    upperRecover differences i.succ =
      upperRecover differences i.castSucc * (differences i.succ)⁻¹ := by
  change Fin.induction (differences 0)⁻¹
      (fun j previous => previous * (differences j.succ)⁻¹) i.succ =
    Fin.induction (differences 0)⁻¹
      (fun j previous => previous * (differences j.succ)⁻¹) i.castSucc *
        (differences i.succ)⁻¹
  rw [Fin.induction_succ]

/-- Recovering after taking upper-oriented differences is the identity. -/
theorem upperRecover_upperForward {n : ℕ} (values : Fin n → G) :
    upperRecover (upperForward values) = values := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero => simp
      | succ i ih =>
          rw [upperRecover_succ, upperForward_succ, ih]
          simp

/-- Taking upper-oriented differences after recursive recovery is the identity. -/
theorem upperForward_upperRecover {n : ℕ} (differences : Fin n → G) :
    upperForward (upperRecover differences) = differences := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · rw [upperForward_succ, upperRecover_succ]
        simp

/-- Upper-oriented rooted differences as an exact noncommutative equivalence. -/
def upperEquiv (n : ℕ) : (Fin n → G) ≃ (Fin n → G) where
  toFun := upperForward
  invFun := upperRecover
  left_inv := upperRecover_upperForward
  right_inv := upperForward_upperRecover

@[simp]
theorem upperEquiv_apply {n : ℕ} (values : Fin n → G) :
    upperEquiv (G := G) n values = upperForward values :=
  rfl

@[simp]
theorem upperEquiv_symm_apply {n : ℕ} (differences : Fin n → G) :
    (upperEquiv (G := G) n).symm differences = upperRecover differences :=
  rfl

/-- Lower-oriented rooted differences:
`D₀ = U₀` and `Dᵢ₊₁ = Uᵢ⁻¹ Uᵢ₊₁`. -/
def lowerForward : ∀ {n : ℕ}, (Fin n → G) → (Fin n → G)
  | 0, _ => fun i => Fin.elim0 i
  | _ + 1, values => Fin.cons (values 0)
      (fun i => (values i.castSucc)⁻¹ * values i.succ)

/-- Explicit recursive recovery from lower-oriented rooted differences:
`U₀ = D₀` and `Uᵢ₊₁ = Uᵢ Dᵢ₊₁`. -/
def lowerRecover : ∀ {n : ℕ}, (Fin n → G) → (Fin n → G)
  | 0, _ => fun i => Fin.elim0 i
  | _ + 1, differences => fun i =>
      Fin.induction (differences 0)
        (fun j previous => previous * differences j.succ) i

@[simp]
theorem lowerForward_zero {n : ℕ} (values : Fin (n + 1) → G) :
    lowerForward values 0 = values 0 := by
  simp [lowerForward]

@[simp]
theorem lowerForward_succ {n : ℕ} (values : Fin (n + 1) → G) (i : Fin n) :
    lowerForward values i.succ = (values i.castSucc)⁻¹ * values i.succ := by
  simp [lowerForward]

@[simp]
theorem lowerRecover_zero {n : ℕ} (differences : Fin (n + 1) → G) :
    lowerRecover differences 0 = differences 0 := by
  simp [lowerRecover]

@[simp]
theorem lowerRecover_succ {n : ℕ} (differences : Fin (n + 1) → G) (i : Fin n) :
    lowerRecover differences i.succ =
      lowerRecover differences i.castSucc * differences i.succ := by
  change Fin.induction (differences 0)
      (fun j previous => previous * differences j.succ) i.succ =
    Fin.induction (differences 0)
      (fun j previous => previous * differences j.succ) i.castSucc *
        differences i.succ
  rw [Fin.induction_succ]

/-- Recovering after taking lower-oriented differences is the identity. -/
theorem lowerRecover_lowerForward {n : ℕ} (values : Fin n → G) :
    lowerRecover (lowerForward values) = values := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      induction i using Fin.induction with
      | zero => simp
      | succ i ih =>
          rw [lowerRecover_succ, lowerForward_succ, ih]
          simp

/-- Taking lower-oriented differences after recursive recovery is the identity. -/
theorem lowerForward_lowerRecover {n : ℕ} (differences : Fin n → G) :
    lowerForward (lowerRecover differences) = differences := by
  cases n with
  | zero =>
      funext i
      exact Fin.elim0 i
  | succ n =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · rw [lowerForward_succ, lowerRecover_succ]
        simp

/-- Lower-oriented rooted differences as an exact noncommutative equivalence. -/
def lowerEquiv (n : ℕ) : (Fin n → G) ≃ (Fin n → G) where
  toFun := lowerForward
  invFun := lowerRecover
  left_inv := lowerRecover_lowerForward
  right_inv := lowerForward_lowerRecover

@[simp]
theorem lowerEquiv_apply {n : ℕ} (values : Fin n → G) :
    lowerEquiv (G := G) n values = lowerForward values :=
  rfl

@[simp]
theorem lowerEquiv_symm_apply {n : ℕ} (differences : Fin n → G) :
    (lowerEquiv (G := G) n).symm differences = lowerRecover differences :=
  rfl

section Measurable

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- Upper-oriented differences are measurable coordinatewise. -/
theorem upperForward_measurable {n : ℕ} :
    Measurable (upperForward : (Fin n → G) → (Fin n → G)) := by
  cases n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [upperForward_zero] using
          (measurable_pi_apply (0 : Fin (n + 1))).inv
      · simpa only [upperForward_succ] using
          (measurable_pi_apply j.succ).inv.mul
            (measurable_pi_apply j.castSucc)

/-- Recursive upper-oriented recovery is measurable coordinatewise. -/
theorem upperRecover_measurable {n : ℕ} :
    Measurable (upperRecover : (Fin n → G) → (Fin n → G)) := by
  cases n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply measurable_pi_iff.mpr
      intro i
      induction i using Fin.induction with
      | zero =>
          simpa only [upperRecover_zero] using
            (measurable_pi_apply (0 : Fin (n + 1))).inv
      | succ i ih =>
          have equality :
              (fun differences : Fin (n + 1) → G => upperRecover differences i.succ) =
                fun differences => upperRecover differences i.castSucc *
                  (differences i.succ)⁻¹ := by
            funext differences
            exact upperRecover_succ differences i
          rw [equality]
          exact ih.mul (measurable_pi_apply i.succ).inv

/-- Upper rooted differences as a measurable equivalence. -/
def upperMeasurableEquiv (n : ℕ) : (Fin n → G) ≃ᵐ (Fin n → G) :=
  MeasurableEquiv.mk (upperEquiv (G := G) n)
    upperForward_measurable upperRecover_measurable

/-- Lower-oriented differences are measurable coordinatewise. -/
theorem lowerForward_measurable {n : ℕ} :
    Measurable (lowerForward : (Fin n → G) → (Fin n → G)) := by
  cases n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply measurable_pi_iff.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [lowerForward_zero] using
          (measurable_pi_apply (0 : Fin (n + 1)))
      · simpa only [lowerForward_succ] using
          (measurable_pi_apply j.castSucc).inv.mul
            (measurable_pi_apply j.succ)

omit [MeasurableInv G] in
/-- Recursive lower-oriented recovery is measurable coordinatewise. -/
theorem lowerRecover_measurable {n : ℕ} :
    Measurable (lowerRecover : (Fin n → G) → (Fin n → G)) := by
  cases n with
  | zero =>
      apply measurable_pi_iff.mpr
      intro i
      exact Fin.elim0 i
  | succ n =>
      apply measurable_pi_iff.mpr
      intro i
      induction i using Fin.induction with
      | zero =>
          simpa only [lowerRecover_zero] using
            (measurable_pi_apply (0 : Fin (n + 1)))
      | succ i ih =>
          have equality :
              (fun differences : Fin (n + 1) → G => lowerRecover differences i.succ) =
                fun differences => lowerRecover differences i.castSucc *
                  differences i.succ := by
            funext differences
            exact lowerRecover_succ differences i
          rw [equality]
          exact ih.mul (measurable_pi_apply i.succ)

/-- Lower rooted differences as a measurable equivalence. -/
def lowerMeasurableEquiv (n : ℕ) : (Fin n → G) ≃ᵐ (Fin n → G) :=
  MeasurableEquiv.mk (lowerEquiv (G := G) n)
    lowerForward_measurable lowerRecover_measurable

end Measurable

end YangMills.Mathematics.RootedGroupDifference
