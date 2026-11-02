/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryLimitGrid

/-! # A finite actual relative-factor grid meets every frozen clopen piece

Only factors valid after the fixed selected hom contribute roots. Invalid
factors, including identically zero specializations, contribute no points.
The original frozen coordinates retain their correlated real values.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling IntegralMixedCanonicalDilation
open Set Polynomial
open scoped Classical
variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type}

noncomputable def coordinateRoots (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (j : Fin (n+1)) (hj : k≤j.val) : Set ℝ :=
  {v | ∃ c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule (by omega : k≤n+1) select)),
    IntegralMixedLimitCoordinate.Valid x hm (rule (by omega : k≤n+1) select)
      (coordinateIndex (by omega : k≤n+1) select j hj) φ c ∧
    ((IntegralMixedLimitCoordinate.factor x hm (rule (by omega : k≤n+1) select)
      (coordinateIndex (by omega : k≤n+1) select j hj) c).map φ.toRingHom).eval v=0}

theorem finite_coordinateRoots (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (j : Fin (n+1)) (hj : k≤j.val) : (coordinateRoots x hm select hk φ j hj).Finite := by
  let A := fun c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source k D t ht m B G) (rule (by omega : k≤n+1) select)) =>
    {v : ℝ | IntegralMixedLimitCoordinate.Valid x hm (rule (by omega : k≤n+1) select)
      (coordinateIndex (by omega : k≤n+1) select j hj) φ c ∧
      ((IntegralMixedLimitCoordinate.factor x hm (rule (by omega : k≤n+1) select)
        (coordinateIndex (by omega : k≤n+1) select j hj) c).map φ.toRingHom).eval v=0}
  have HA : ∀ c, (A c).Finite := by
    intro c
    by_cases hc : IntegralMixedLimitCoordinate.Valid x hm (rule (by omega : k≤n+1) select)
        (coordinateIndex (by omega : k≤n+1) select j hj) φ c
    · apply (IntegralMixedLimitCoordinate.finite_roots x hm _ _ φ c hc).subset
      intro v hv
      change (IntegralMixedLimitCoordinate.factor x hm _ _ c).eval₂ φ.toRingHom v=0
      simpa only [Polynomial.eval_map] using hv.2
    · have HE : A c=∅ := by ext v; simp only [A,Set.mem_ofPred_eq,hc,false_and,Set.mem_empty_iff_false]
      rw [HE]
      exact Set.finite_empty
  exact (Set.finite_iUnion HA).subset (by intro v hv; simpa only [coordinateRoots,Set.mem_ofPred_eq,Set.mem_iUnion,A] using hv)

noncomputable def grid (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a : Fin n → ℝ) :
    Set (Fin (n+1) → ℝ) :=
  Set.pi Set.univ (fun j => if hj : j.val<k then {a ⟨j.val,by omega⟩}
    else coordinateRoots x hm select hk φ j (by omega))

theorem finite_grid (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a : Fin n → ℝ) :
    (grid x hm select hk φ a).Finite := by
  let A := fun j : Fin (n+1) => if hj : j.val<k then {a ⟨j.val,by omega⟩}
    else coordinateRoots x hm select hk φ j (by omega)
  have HA : ∀ j, (A j).Finite := by
    intro j
    dsimp only [A]
    split_ifs
    · exact Set.finite_singleton _
    · exact finite_coordinateRoots x hm select hk φ j _
  apply (Set.Finite.pi' HA).subset
  intro f hf j
  exact hf j (Set.mem_univ _)

theorem meets_grid (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (HG : x.bank.Bounds G) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (values : Fin m → ℝ) (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (ha : t.arity≤n) (hk : k≤n) (hD : 0<D) (select : Fin k → Fin m) (a : Fin n → ℝ)
    (Hparam : ∀ j : Fin n, ∀ hj : j.val<k, a j=values (select ⟨j.val,hj⟩))
    (C : Set (slice (polynomial n t) k a)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) k a) (hx0 : x0∈C) :
    ∃ b : slice (polynomial n t) k a, b∈C ∧ Fin.snoc b.val 0∈grid x hm select hk φ a := by
  obtain ⟨b,hb,hr⟩ := meets_selected_factors x hm HG φ values H ha hk hD select a Hparam C hC x0 hx0
  have HF : ∀ j : Fin (n+1), ∀ hj : j.val<k,
      (Fin.snoc b.val (0:ℝ) : Fin (n+1) → ℝ) j=a ⟨j.val,by omega⟩ := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · intro hj
      have HN : n<k := hj
      omega
    · intro hj
      change i.val<k at hj
      rw [Fin.snoc_castSucc]
      change b.val i=a i
      exact b.property.2 i hj
  refine ⟨b,hb,?_⟩
  intro j _
  change _∈(if hj : j.val<k then {_} else _)
  split_ifs with hj
  · exact HF j hj
  · obtain ⟨c,hc⟩ := IntegralMixedLimitCoordinate.exists_valid x hm (rule (by omega : k≤n+1) select)
      (coordinateIndex (by omega : k≤n+1) select j (by omega)) φ
    exact ⟨c,hc,hr j (by omega) c hc⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
