/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.CovariantLocalObservableFamily

/-!
# Finite covariant local-observable multiplets

Streater–Wightman, printed p. 99, axiom II, equations (3-4)–(3-5), treats a field as a
finite set of components transforming through one finite-dimensional representation. Translations
act on the test argument and do not mix components. The examples immediately following distinguish
scalar, vector, and spinorial transformation laws.

This module packages that reusable requirement on the same common domain and local-observable
family already used by the scalar and stress-tensor surfaces. The base interface represents the
Poincaré lift group and therefore permits nontrivial central action appropriate to spinorial
multiplets. A separate Lorentz-tensor strengthening requires the mixing to factor through the exact
projected Lorentz transformation. A further predicate-indexed cover interface can require any
explicit subset of a proposed observable family to occur in finite lift-covariant multiplets without
silently excluding spinorial cover-kernel action. These interfaces construct no independent field,
representation, theory, or mass gap. Kinematic component mixing here is distinct from renormalization/operator mixing.
-/

namespace YangMills.Minkowski

universe uLift uH uLabel

/-- A nonempty finite component family transforming through one strongly continuous complex-linear
representation of the exact Poincaré lift group. Translation lifts have trivial component mixing;
their affine action remains present in the exact Schwartz pullback. -/
structure FiniteLiftCovariantObservableMultipletData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D)
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] where
  /-- Existing local-observable label assigned to each finite component. Injectivity is not required:
  symmetric tensor presentations may deliberately identify indices. -/
  componentLabel : ι → family.Label
  /-- One exact complex-linear representation controlling all component mixing. -/
  mixingRepresentation : G →* Module.End ℂ (ι → ℂ)
  /-- Pointwise strong continuity of the finite-dimensional mixing representation. -/
  mixing_stronglyContinuous : ∀ v : ι → ℂ,
    Continuous (fun g => mixingRepresentation g v)
  /-- Physical translation lifts do not mix the finite component indices. -/
  mixing_translation : ∀ a : Spacetime d,
    mixingRepresentation (lift.translation (Multiplicative.ofAdd a)) = 1
  /-- Exact finite-component covariance on the same physical domain, operators, and inverse-affine
  test pullback. The image of the basis vector at `i` gives the coefficients of the transformed
  component: under the source notation this basis-image coefficient is `S_{ij}(A⁻¹)`. Bundling
  these coefficients as `mixingRepresentation` therefore gives the same multiplication order as
  the physical lift representation rather than an accidental opposite action. -/
  component_covariant : ∀ i g f ψ,
    D.domainUnitary g
        (family.operator (componentLabel i) f ((D.domainUnitary g).symm ψ)) =
      ∑ j, (mixingRepresentation g (Pi.single i 1) j) •
        family.operator (componentLabel j)
          (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ
  /-- At least one component acts nontrivially and differs from the unit field. -/
  nontrivial_component : ∃ i f ψ,
    family.operator (componentLabel i) f ψ ≠ 0 ∧
    family.operator (componentLabel i) f ψ ≠ family.operator family.unitLabel f ψ

/-- Tensorial strengthening of a finite lift-covariant multiplet: component mixing depends only on
the projected Lorentz transformation. This excludes nontrivial cover-kernel action and is therefore
not imposed on the base interface used for possible spinorial multiplets. -/
structure FiniteLorentzCovariantObservableMultipletData
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData D)
    (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    extends FiniteLiftCovariantObservableMultipletData family ι where
  mixing_eq_of_projectedLorentz_eq : ∀ g h,
    (lift.projection g).lorentz = (lift.projection h).lorentz →
      mixingRepresentation g = mixingRepresentation h

/-- Coverage of an explicit label subset by nonempty finite lift-covariant multiplets. The family
may contain arbitrarily many labels and multiplets, but every selected individual field has a finite
component transformation law. Using lift-covariant rather than projected-Lorentz multiplets keeps
this reusable surface valid for spinorial as well as tensorial fields. -/
structure FiniteLiftCovariantObservableCoverData
    {d : EuclideanDimension} {G : Type uLift}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D)
    (coveredLabel : Set family.Label) where
  /-- Index of finite multiplets. It is forced nonempty whenever the selected label set is inhabited. -/
  Multiplet : Type uLabel
  /-- Multiplet `m` has `extraComponentCount m + 1` components, hence is definitionally nonempty. -/
  extraComponentCount : Multiplet → ℕ
  /-- Exact finite lift-covariant multiplet data inside the same observable family. -/
  multiplet : ∀ m,
    FiniteLiftCovariantObservableMultipletData family (Fin (extraComponentCount m + 1))
  /-- Every selected family label occurs as an exact component of one supplied multiplet. -/
  covers : ∀ A, A ∈ coveredLabel →
    ∃ (m : Multiplet) (i : Fin (extraComponentCount m + 1)),
      (multiplet m).componentLabel i = A

/-- Coverage of an explicit bosonic/tensorial label subset by nonempty finite multiplets whose
mixing factors through the projected Lorentz transformation. This is the appropriate strengthening
for gauge-invariant Yang–Mills local observables; spinorial fields require the lift-covariant cover
and a separate graded-locality interface. -/
structure FiniteLorentzCovariantObservableCoverData
    {d : EuclideanDimension} {G : Type uLift}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    (family : TemperedLocalObservableFamilyData.{uLift, uH, uLabel} D)
    (coveredLabel : Set family.Label) where
  Multiplet : Type uLabel
  extraComponentCount : Multiplet → ℕ
  multiplet : ∀ m,
    FiniteLorentzCovariantObservableMultipletData family (Fin (extraComponentCount m + 1))
  covers : ∀ A, A ∈ coveredLabel →
    ∃ (m : Multiplet) (i : Fin (extraComponentCount m + 1)),
      (multiplet m).componentLabel i = A

/-- The mixing representation has the exact identity action. -/
@[simp] theorem FiniteLiftCovariantObservableMultipletData.mixingRepresentation_one
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (data : FiniteLiftCovariantObservableMultipletData family ι) :
    data.mixingRepresentation 1 = 1 :=
  data.mixingRepresentation.map_one

/-- Multiplet mixing composes in the same group order as the physical representation. -/
@[simp] theorem FiniteLiftCovariantObservableMultipletData.mixingRepresentation_mul
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (data : FiniteLiftCovariantObservableMultipletData family ι) (g h : G) :
    data.mixingRepresentation (g * h) =
      data.mixingRepresentation g * data.mixingRepresentation h :=
  data.mixingRepresentation.map_mul g h

private def trivialFiniteMixingRepresentation (G ι : Type*)
    [Group G] [Fintype ι] : G →* Module.End ℂ (ι → ℂ) where
  toFun := fun _ => 1
  map_one' := rfl
  map_mul' := fun _ _ => (one_mul 1).symm

/-- The existing distinguished nontrivial scalar field gives an exact one-component Lorentz
multiplet with trivial mixing. This is a derived adapter, not a new field witness. -/
noncomputable def CovariantLocalObservableFamilyData.nontrivialFiniteScalarMultiplet
    {d : EuclideanDimension} {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {lift : ProperOrthochronousPoincareLiftData d G}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {U : StronglyContinuousUnitaryPoincareRepresentation lift H}
    {vacuumData : PoincareInvariantVacuumData U}
    {D : CommonInvariantDomainData vacuumData}
    {family : TemperedLocalObservableFamilyData D}
    (covariance : CovariantLocalObservableFamilyData family) :
    FiniteLorentzCovariantObservableMultipletData family (Fin 1) where
  componentLabel := fun _ => family.nontrivialLabel
  mixingRepresentation := trivialFiniteMixingRepresentation G (Fin 1)
  mixing_stronglyContinuous := fun _ => continuous_const
  mixing_translation := fun _ => rfl
  component_covariant := by
    intro i g f ψ
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa [trivialFiniteMixingRepresentation] using
      covariance.nontrivial_operator_covariant g f ψ
  nontrivial_component := by
    rcases family.nontrivial_operator_witness with ⟨f, ψ, hzero, hunit⟩
    exact ⟨0, f, ψ, hzero, hunit⟩
  mixing_eq_of_projectedLorentz_eq := fun _ _ _ => rfl

end YangMills.Minkowski
