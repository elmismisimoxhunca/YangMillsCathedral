/-
Copyright (c) 2026 Sebastian Rodrigo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Rodrigo
-/

import YangMills.Minkowski.FiniteCovariantObservableMultiplet

/-!
# Hostile probes for finite covariant observable multiplets

These probes expose nonempty finite indices, genuine representation laws, strong continuity,
translation-trivial mixing, exact same-chain covariance, component anti-vacuity, tensorial Lorentz
factorization, and exact scalar recovery. No multiplet datum is constructed independently.
-/

namespace YangMills.Minkowski.FiniteCovariantObservableMultiplet.Probes

variable
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

/-- The component index cannot be empty. -/
theorem exact_nonempty_component_index
    (data : FiniteLiftCovariantObservableMultipletData family ι) :
    ∃ i : ι, data.componentLabel i = data.componentLabel i :=
  ⟨Classical.choice inferInstance, rfl⟩

/-- Identity mixing is forced by the genuine representation, not supplied independently. -/
theorem exact_representation_identity
    (data : FiniteLiftCovariantObservableMultipletData family ι) :
    data.mixingRepresentation 1 = 1 :=
  data.mixingRepresentation_one

/-- Mixing at a product is exact composition in the physical group order. -/
theorem exact_representation_composition
    (data : FiniteLiftCovariantObservableMultipletData family ι) (g h : G) :
    data.mixingRepresentation (g * h) =
      data.mixingRepresentation g * data.mixingRepresentation h :=
  data.mixingRepresentation_mul g h

/-- The supplied representation is strongly continuous on every exact component vector. -/
theorem exact_strong_continuity
    (data : FiniteLiftCovariantObservableMultipletData family ι) (v : ι → ℂ) :
    Continuous (fun g => data.mixingRepresentation g v) :=
  data.mixing_stronglyContinuous v

/-- Translation lifts cannot carry unrelated component-mixing matrices. -/
theorem exact_translation_trivial_mixing
    (data : FiniteLiftCovariantObservableMultipletData family ι)
    (a : Spacetime d) :
    data.mixingRepresentation (lift.translation (Multiplicative.ofAdd a)) = 1 :=
  data.mixing_translation a

/-- Covariance uses the exact physical domain unitary, existing family operator, finite mixing
representation, and projected inverse-affine test pullback. -/
theorem exact_same_chain_component_covariance
    (data : FiniteLiftCovariantObservableMultipletData family ι)
    (i : ι) (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain) :
    D.domainUnitary g
        (family.operator (data.componentLabel i) f ((D.domainUnitary g).symm ψ)) =
      ∑ j, (data.mixingRepresentation g (Pi.single i 1) j) •
        family.operator (data.componentLabel j)
          (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ :=
  data.component_covariant i g f ψ

/-- A nonempty index with only zero/unit behavior cannot pass as a nontrivial multiplet. -/
theorem exact_nontrivial_component
    (data : FiniteLiftCovariantObservableMultipletData family ι) :
    ∃ i f ψ,
      family.operator (data.componentLabel i) f ψ ≠ 0 ∧
      family.operator (data.componentLabel i) f ψ ≠ family.operator family.unitLabel f ψ :=
  data.nontrivial_component

/-- Tensorial multiplets cannot distinguish lift elements with the same projected Lorentz part. -/
theorem exact_lorentz_factorization
    (data : FiniteLorentzCovariantObservableMultipletData family ι)
    (g h : G)
    (hprojection : (lift.projection g).lorentz = (lift.projection h).lorentz) :
    data.mixingRepresentation g = data.mixingRepresentation h :=
  data.mixing_eq_of_projectedLorentz_eq g h hprojection

/-- The existing distinguished scalar label yields exactly one component and trivial mixing; no
unrelated operator family is introduced by the adapter. -/
theorem exact_scalar_specialization
    (covariance : CovariantLocalObservableFamilyData family) :
    (∀ i : Fin 1,
      covariance.nontrivialFiniteScalarMultiplet.componentLabel i = family.nontrivialLabel) ∧
    (∀ g : G,
      covariance.nontrivialFiniteScalarMultiplet.mixingRepresentation g = 1) := by
  constructor
  · intro i
    rfl
  · intro g
    rfl

/-- Every selected label is an exact component of some finite lift-covariant multiplet. -/
theorem exact_selected_label_coverage
    {coveredLabel : Set family.Label}
    (cover : FiniteLiftCovariantObservableCoverData family coveredLabel)
    (A : family.Label) (hA : A ∈ coveredLabel) :
    ∃ (m : cover.Multiplet) (i : Fin (cover.extraComponentCount m + 1)),
      (cover.multiplet m).componentLabel i = A :=
  cover.covers A hA

/-- The multiplet index cannot be vacuous whenever the selected label set is inhabited. -/
theorem exact_cover_has_multiplet
    {coveredLabel : Set family.Label}
    (cover : FiniteLiftCovariantObservableCoverData family coveredLabel)
    (A : family.Label) (hA : A ∈ coveredLabel) :
    Nonempty cover.Multiplet := by
  rcases cover.covers A hA with ⟨m, _i, _hlabel⟩
  exact ⟨m⟩

/-- Coverage supplies exact same-chain covariance for the selected original label, not merely for an
unrelated copied operator family. -/
theorem exact_covered_label_covariance
    {coveredLabel : Set family.Label}
    (cover : FiniteLiftCovariantObservableCoverData family coveredLabel)
    (A : family.Label) (hA : A ∈ coveredLabel) :
    ∃ (m : cover.Multiplet) (i : Fin (cover.extraComponentCount m + 1)),
      (cover.multiplet m).componentLabel i = A ∧
      ∀ (g : G) (f : ScalarMinkowskiSchwartzTestFunction d) (ψ : D.domain),
        D.domainUnitary g
            (family.operator A f ((D.domainUnitary g).symm ψ)) =
          ∑ j,
            ((cover.multiplet m).mixingRepresentation g (Pi.single i 1) j) •
              family.operator ((cover.multiplet m).componentLabel j)
                (pullbackScalarMinkowskiSchwartzTestFunction d (lift.projection g) f) ψ := by
  rcases cover.covers A hA with ⟨m, i, hlabel⟩
  refine ⟨m, i, hlabel, ?_⟩
  intro g f ψ
  rw [← hlabel]
  exact (cover.multiplet m).component_covariant i g f ψ

end YangMills.Minkowski.FiniteCovariantObservableMultiplet.Probes
