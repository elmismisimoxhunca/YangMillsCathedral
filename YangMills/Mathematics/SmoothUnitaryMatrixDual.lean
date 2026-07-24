/-
Copyright (c) 2026 YangMillsDefinition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YangMillsDefinition contributors
-/
import YangMills.Mathematics.UnitaryMatrixDual
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The smooth coordinate unitary dual and its continuous comparison

Lévy's compact-Lie-group dual is phrased using smooth finite-dimensional representations. This file
therefore refines the existing continuous coordinate bundle by requiring exact `ContMDiff` matrix
coordinates, quotients smooth bundles by the same representation equivalence, and constructs the
canonical map

`SmoothUnitaryMatrixDual E G → UnitaryMatrixDual G`.

The map is injective because both quotients use the same intertwining equivalence. Its image is
characterized by the explicit predicate `UnitaryMatrixDual.HasSmoothRepresentative`. Surjectivity is
proved equivalent to every continuous coordinate class having such a smooth representative; no
surjectivity or automatic continuity-to-smoothness theorem is assumed.

Thus this file formalizes the exact remaining comparison gap without identifying the two duals by
fiat. It does not prove Peter–Weyl density, countability, or infinite-series Plancherel.
-/

namespace YangMills
namespace Mathematics

open scoped Manifold ContDiff

noncomputable section

universe uE uG

variable {E:Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
 {G:Type uG} [Group G] [TopologicalSpace G] [ChartedSpace E G]

/-- A continuous irreducible unitary matrix representation whose exact matrix coordinate map is
smooth in the supplied manifold model. -/
structure SmoothUnitaryIrreducibleMatrixRepresentation
 (E:Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
 (G:Type uG) [Group G] [TopologicalSpace G] [ChartedSpace E G]
 extends ContinuousUnitaryIrreducibleMatrixRepresentation G where
 representation_contMDiff : ContMDiff (modelWithCornersSelf ℝ E)
  (modelWithCornersSelf ℝ
   (Fin toContinuousUnitaryIrreducibleMatrixRepresentation.dimension →
    Fin toContinuousUnitaryIrreducibleMatrixRepresentation.dimension → ℂ)) ∞
  (fun g i j => toContinuousUnitaryIrreducibleMatrixRepresentation.representation g i j)

def SmoothUnitaryIrreducibleMatrixRepresentation.IsEquivalent
 (ρ σ:SmoothUnitaryIrreducibleMatrixRepresentation E G) : Prop :=
 ρ.toContinuousUnitaryIrreducibleMatrixRepresentation.IsEquivalent
  σ.toContinuousUnitaryIrreducibleMatrixRepresentation

theorem SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_refl
 (ρ:SmoothUnitaryIrreducibleMatrixRepresentation E G) : ρ.IsEquivalent ρ :=
 ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_refl _

theorem SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm
 {ρ σ:SmoothUnitaryIrreducibleMatrixRepresentation E G} :
 ρ.IsEquivalent σ → σ.IsEquivalent ρ :=
 ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm

theorem SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_trans
 {ρ σ τ:SmoothUnitaryIrreducibleMatrixRepresentation E G} :
 ρ.IsEquivalent σ → σ.IsEquivalent τ → ρ.IsEquivalent τ :=
 ContinuousUnitaryIrreducibleMatrixRepresentation.isEquivalent_trans

instance smoothUnitaryIrreducibleMatrixRepresentationSetoid :
 Setoid (SmoothUnitaryIrreducibleMatrixRepresentation E G) where
 r := SmoothUnitaryIrreducibleMatrixRepresentation.IsEquivalent
 iseqv := ⟨
  SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_refl,
  SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_symm,
  SmoothUnitaryIrreducibleMatrixRepresentation.isEquivalent_trans⟩

/-- Equivalence classes of smooth irreducible unitary matrix representations. -/
def SmoothUnitaryMatrixDual :=
 Quotient (smoothUnitaryIrreducibleMatrixRepresentationSetoid (E:=E) (G:=G))

def smoothUnitaryMatrixDualClass
 (ρ:SmoothUnitaryIrreducibleMatrixRepresentation E G) :
 SmoothUnitaryMatrixDual (E:=E) (G:=G) := Quotient.mk _ ρ

/-- Forgetting smoothness induces the canonical map from the smooth coordinate dual to the
continuous coordinate dual. -/
def smoothUnitaryMatrixDualToUnitaryMatrixDual :
 SmoothUnitaryMatrixDual (E:=E) (G:=G) → UnitaryMatrixDual G :=
 Quotient.map
  SmoothUnitaryIrreducibleMatrixRepresentation.toContinuousUnitaryIrreducibleMatrixRepresentation
  (by
   intro ρ σ h
   change ρ.toContinuousUnitaryIrreducibleMatrixRepresentation.IsEquivalent
    σ.toContinuousUnitaryIrreducibleMatrixRepresentation at h
   exact h)

@[simp] theorem smoothUnitaryMatrixDualToUnitaryMatrixDual_class
 (ρ:SmoothUnitaryIrreducibleMatrixRepresentation E G) :
 smoothUnitaryMatrixDualToUnitaryMatrixDual (smoothUnitaryMatrixDualClass ρ) =
 unitaryMatrixDualClass ρ.toContinuousUnitaryIrreducibleMatrixRepresentation := by
 rfl

/-- The smooth-to-continuous dual map is injective because both quotients use exact representation
equivalence. -/
theorem smoothUnitaryMatrixDualToUnitaryMatrixDual_injective :
 Function.Injective (smoothUnitaryMatrixDualToUnitaryMatrixDual (E:=E) (G:=G)) := by
 intro q r h
 induction q using Quotient.inductionOn with
 | _ ρ =>
  induction r using Quotient.inductionOn with
  | _ σ =>
   apply Quotient.sound
   change ρ.IsEquivalent σ
   exact (unitaryMatrixDualClass_eq_iff
    ρ.toContinuousUnitaryIrreducibleMatrixRepresentation
    σ.toContinuousUnitaryIrreducibleMatrixRepresentation).mp h

/-- A continuous coordinate-dual class lies in the image of the smooth coordinate dual. -/
def UnitaryMatrixDual.HasSmoothRepresentative
 (q:UnitaryMatrixDual G) : Prop :=
 ∃s:SmoothUnitaryMatrixDual (E:=E) (G:=G),
  smoothUnitaryMatrixDualToUnitaryMatrixDual s=q

theorem unitaryMatrixDualClass_hasSmoothRepresentative
 (ρ:SmoothUnitaryIrreducibleMatrixRepresentation E G) :
 (unitaryMatrixDualClass
   ρ.toContinuousUnitaryIrreducibleMatrixRepresentation).HasSmoothRepresentative
    (E:=E) := by
 refine ⟨smoothUnitaryMatrixDualClass ρ, ?_⟩
 exact smoothUnitaryMatrixDualToUnitaryMatrixDual_class ρ

theorem unitaryMatrixDual_hasSmoothRepresentative_iff_mem_range
 (q:UnitaryMatrixDual G) :
 q.HasSmoothRepresentative (E:=E) ↔
 q∈Set.range (smoothUnitaryMatrixDualToUnitaryMatrixDual (E:=E) (G:=G)) := by
 rfl

/-- A smooth-representative class predicate can be eliminated to one explicitly bundled smooth
irreducible presentation of the given continuous-dual class. -/
theorem UnitaryMatrixDual.hasSmoothRepresentative_iff_exists_representation
 (q:UnitaryMatrixDual G) :
 q.HasSmoothRepresentative (E:=E) ↔
 ∃ρ:SmoothUnitaryIrreducibleMatrixRepresentation E G,
  unitaryMatrixDualClass
   ρ.toContinuousUnitaryIrreducibleMatrixRepresentation=q := by
 constructor
 · rintro ⟨smoothClass, hsmoothClass⟩
   induction smoothClass using Quotient.inductionOn with
   | _ ρ => exact ⟨ρ, hsmoothClass⟩
 · rintro ⟨ρ, hρ⟩
   refine ⟨smoothUnitaryMatrixDualClass ρ, ?_⟩
   rw [smoothUnitaryMatrixDualToUnitaryMatrixDual_class]
   exact hρ

/-- Surjectivity of the comparison map is exactly the unresolved assertion that every continuous
coordinate class has a smooth representative. -/
theorem smoothUnitaryMatrixDual_surjective_iff_all_hasSmoothRepresentative :
 Function.Surjective (smoothUnitaryMatrixDualToUnitaryMatrixDual (E:=E) (G:=G)) ↔
 ∀q:UnitaryMatrixDual G,q.HasSmoothRepresentative (E:=E) := by
 rfl

end

end Mathematics
end YangMills
