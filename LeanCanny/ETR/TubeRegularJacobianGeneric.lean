/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianBudget
public import LeanCanny.ETR.TubeRegularFiber
public import LeanCanny.Algebra.GenericProjectionJacobian
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # The actual native tube Jacobian and the generic critical Jacobian

Specializing direction and perturbation variables commutes with differentiation
in reciprocal and point variables. The actual square integer Jacobian therefore
agrees with the generic extended Jacobian after the same row/column reindexing.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularJacobianGeneric
open LeanCanny.Encoding LeanCanny.Algebra Geometry MvPolynomial
open TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] Matrix.det
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

variable {L : Type*} [Field L]

noncomputable def spatialVariable (bits : List Bool) :
    Option (TubeSource.Coordinate bits) → TubeRegularSource.Variable bits
  | none => none
  | some i => some (.inl (.inl i))

noncomputable def rowEquiv (bits : List Bool) :
    TubeRegularSource.Index bits ≃ Option (TubeSource.Coordinate bits) :=
  Equiv.optionCongr (Equiv.optionSubtypeNe (TubePolynomial.base _))

theorem coordinate_eq (bits : List Bool) (j : TubeRegularSource.Index bits) :
    TubeRegularJacobianBudget.coordinate bits j = spatialVariable bits (rowEquiv bits j) := by
  cases j <;> rfl

noncomputable def nativeAssignment (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L) : TubeRegularSource.Variable bits → L :=
  fun i => i.elim (z none) (TubeMacaulay.values _ φ (fun k => z (some k)))

noncomputable def substitution (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (i : TubeRegularSource.Variable bits) : MvPolynomial (Option (TubeSource.Coordinate bits)) L :=
  (TubeMacaulay.image (TubeIndexed.arity bits) i).map φ

noncomputable def specialize (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L) :
    MvPolynomial (TubeRegularSource.Variable bits) ℤ →+* MvPolynomial (Option (TubeSource.Coordinate bits)) L :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Int.castRingHom L)) (substitution bits φ)

@[simp] theorem specialize_X (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (i : TubeRegularSource.Variable bits) : specialize bits φ (X i) = substitution bits φ i :=
  MvPolynomial.eval₂Hom_X' _ _ _

@[simp] theorem specialize_C (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L) (a : ℤ) :
    specialize bits φ (C a) = C ((Int.castRingHom L) a) :=
  MvPolynomial.eval₂Hom_C _ _ _

theorem pderiv_substitution (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (i : TubeRegularSource.Variable bits) (j : Option (TubeSource.Coordinate bits)) :
    pderiv j (substitution bits φ i) = if i = spatialVariable bits j then 1 else 0 := by
  rcases i with _ | ((i | i) | p) <;> cases j <;>
    simp only [substitution, TubeMacaulay.image, MvPolynomial.map_X, MvPolynomial.map_C]
  all_goals simp only [MvPolynomial.pderiv_X, Pi.single_apply, spatialVariable,
    Option.some.injEq, Sum.inl.injEq, Option.some_ne_none,
    Sum.inr_ne_inl, reduceCtorEq]
  all_goals change pderiv _ (MvPolynomial.C _) = _
  all_goals rw [MvPolynomial.pderiv_C, ite_false]

theorem specialize_pderiv (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ)
    (j : Option (TubeSource.Coordinate bits)) :
    specialize bits φ (pderiv (spatialVariable bits j) p) = pderiv j (specialize bits φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.pderiv_C, map_zero, specialize_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [pderiv_mul, pderiv_X, Pi.single_apply, map_add, map_mul, hp,
      specialize_X, pderiv_substitution]
    split_ifs <;> simp only [map_one, map_zero]

theorem eval_substitution (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L) (i : TubeRegularSource.Variable bits) :
    aeval z (substitution bits φ i) = nativeAssignment bits φ z i := by
  rcases i with _ | ((i | i) | p) <;>
    simp only [substitution, TubeMacaulay.image, MvPolynomial.map_X, MvPolynomial.map_C,
      aeval_X, nativeAssignment,
      Option.elim_none, Option.elim_some, TubeMacaulay.values, Sum.elim_inl, Sum.elim_inr]
  all_goals change aeval _ (MvPolynomial.C _) = _
  all_goals rw [aeval_C]; rfl

theorem eval_specialize (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ) :
    aeval z (specialize bits φ p) = p.eval₂ (Int.castRingHom L) (nativeAssignment bits φ z) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [specialize_C, aeval_C, MvPolynomial.eval₂_C, Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq => simp only [map_add, MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, hp, specialize_X, eval_substitution]

theorem eval_specialize_pderiv (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ)
    (j : Option (TubeSource.Coordinate bits)) :
    (pderiv (spatialVariable bits j) p).eval₂ (Int.castRingHom L) (nativeAssignment bits φ z) =
      aeval z (pderiv j (specialize bits φ p)) := by
  rw [← specialize_pderiv, eval_specialize]

theorem eval_regular (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L) (i : TubeRegularSource.Index bits) :
    (TubeRegularSource.polynomial bits s i).eval₂ (Int.castRingHom L)
      (nativeAssignment bits φ z) =
      aeval z (GenericProjectionJacobian.equation
        (TubeRegularFiber.specializedPolynomial bits s φ) (TubePolynomial.base _) 0
        (TubeRegularFiber.direction bits φ) (rowEquiv bits i)) := by
  cases i with
  | none =>
    change (ReciprocalEquation.polynomial _ _).eval₂ _
      (fun i => i.elim (z none) (TubeMacaulay.values _ φ (fun k => z (some k)))) = _
    rw [ReciprocalEquation.eval]
    change z none * (pderiv (TubeRegularSource.base (TubeIndexed.arity bits))
      (TubeSource.integerProjection bits s none)).eval₂ (Int.castRingHom L)
        (TubeMacaulay.values _ φ (fun k => z (some k))) - 1 = _
    rw [TubeRegularFiber.eval_base_derivative]
    simp only [rowEquiv, Equiv.optionCongr_apply, Option.map_none, GenericProjectionJacobian.equation,
      map_sub, map_mul, aeval_X, GenericProjectionFinite.eval_liftPolynomial,
      map_one, TubeRegularFiber.eval_specialized_partial]
    rfl
  | some i =>
    change (rename some (TubeSource.integerProjection bits s i)).eval₂ _ _ = _
    rw [MvPolynomial.eval₂_rename]
    change (TubeSource.integerProjection bits s i).eval₂ _
      (TubeMacaulay.values _ φ (fun k => z (some k))) = _
    cases i with
    | none =>
      rw [TubeRegularFiber.eval_level]
      simp only [rowEquiv, Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_none,
        GenericProjectionJacobian.equation, ite_true, map_sub,
        GenericProjectionFinite.eval_liftPolynomial, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, sub_zero,
        TubeRegularFiber.eval_specialized]
      rfl
    | some i =>
      rw [TubeRegularFiber.eval_partial]
      simp only [rowEquiv, Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some,
        GenericProjectionJacobian.equation, i.property, ite_false, map_sub, map_mul,
        GenericProjectionFinite.eval_liftPolynomial, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply,
        TubeRegularFiber.eval_specialized_partial]
      rfl

theorem specialize_regular [Infinite L] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (i : TubeRegularSource.Index bits) :
    specialize bits φ (TubeRegularSource.polynomial bits s i) =
      GenericProjectionJacobian.equation (TubeRegularFiber.specializedPolynomial bits s φ)
        (TubePolynomial.base _) 0 (TubeRegularFiber.direction bits φ) (rowEquiv bits i) := by
  apply MvPolynomial.funext
  intro z
  change aeval z _ = aeval z _
  rw [eval_specialize, eval_regular]

theorem matrix_eq [Infinite L] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L) :
    (fun i j => (TubeRegularJacobianBudget.matrix bits s i j).eval₂ (Int.castRingHom L)
      (nativeAssignment bits φ z)) =
      (GenericProjectionJacobian.extended (TubeRegularFiber.specializedPolynomial bits s φ)
        (TubePolynomial.base _) (TubeRegularFiber.direction bits φ)
        (fun k => z (some k)) (z none)).submatrix (rowEquiv bits) (rowEquiv bits) := by
  have he := GenericProjectionJacobian.formalJacobian_eq
    (TubeRegularFiber.specializedPolynomial bits s φ) (TubePolynomial.base _) (0 : L)
    (TubeRegularFiber.direction bits φ) (fun k => z (some k)) (z none)
  have hz : (fun k : Option (TubeSource.Coordinate bits) =>
      k.elim (z none) (fun k => z (some k))) = z := by funext k; cases k <;> rfl
  rw [hz] at he
  ext i j
  change (pderiv (TubeRegularJacobianBudget.coordinate bits j)
    (TubeRegularSource.polynomial bits s i)).eval₂ _ _ = _
  rw [coordinate_eq, eval_specialize_pderiv, specialize_regular]
  exact congrFun (congrFun he (rowEquiv bits i)) (rowEquiv bits j)

theorem eval_determinant [Infinite L] (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (z : Option (TubeSource.Coordinate bits) → L) :
    (TubeRegularJacobianBudget.polynomial bits s).eval₂ (Int.castRingHom L)
      (nativeAssignment bits φ z) =
      (GenericProjectionJacobian.extended (TubeRegularFiber.specializedPolynomial bits s φ)
        (TubePolynomial.base _) (TubeRegularFiber.direction bits φ)
        (fun k => z (some k)) (z none)).det := by
  rw [TubeRegularJacobianBudget.eval_polynomial]
  change Matrix.det (fun i j => (TubeRegularJacobianBudget.matrix bits s i j).eval₂ _ _) = _
  rw [matrix_eq, Matrix.det_submatrix_equiv_self]

section IndependentLevel
variable {K : Type*} [Field K] [Algebra K L]

theorem extended_constShift {bits : List Bool} (p : MvPolynomial (TubeSource.Coordinate bits) K)
    (base : TubeSource.Coordinate bits) (alpha : L)
    (v x : TubeSource.Coordinate bits → L) (u : L) :
    GenericProjectionJacobian.extended (p.map (algebraMap K L) - C alpha) base v x u =
      GenericProjectionJacobian.extended p base v x u := by
  ext i j
  cases i <;> cases j <;>
    simp only [GenericProjectionJacobian.extended, GenericProjectionJacobian.spatial,
      map_sub, MvPolynomial.pderiv_C, MvPolynomial.pderiv_map, sub_zero,
      aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_map, RingHom.id_comp]

/-- Independence of the level and nonbase direction parameters rules out roots
of the actual integer equations together with their actual Jacobian determinant. -/
theorem determinant_ne_zero_of_independent [CharZero K] [Infinite L]
    (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (TubeIndexed.arity bits) →+* L)
    (p : MvPolynomial (TubeSource.Coordinate bits) K) (alpha : L)
    (hpoly : TubeRegularFiber.specializedPolynomial bits s φ = p.map (algebraMap K L) - C alpha)
    (hb : TubeRegularFiber.direction bits φ (TubePolynomial.base _) = 1)
    (hind : AlgebraicIndependent K (GenericProjectionJacobian.parameters
      (TubePolynomial.base _) alpha (TubeRegularFiber.direction bits φ)))
    (z : Option (TubeSource.Coordinate bits) → L)
    (hz : ∀ i, (TubeRegularSource.polynomial bits s i).eval₂ (Int.castRingHom L)
      (nativeAssignment bits φ z) = 0) :
    (TubeRegularJacobianBudget.polynomial bits s).eval₂ (Int.castRingHom L)
      (nativeAssignment bits φ z) ≠ 0 := by
  have hr := (TubeRegularSource.root_iff bits s (Int.castRingHom L)
    (TubeMacaulay.values _ φ (fun k => z (some k))) (z none)).mp hz
  have hp : aeval (fun k => z (some k)) p = alpha := by
    have hl := (TubeRegularFiber.eval_level bits s φ (fun k => z (some k))).symm.trans (hr.1.1 none)
    rw [← TubeRegularFiber.eval_specialized, hpoly] at hl
    simpa only [map_sub, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      aeval_def, MvPolynomial.eval₂_map, RingHom.id_comp, MvPolynomial.eval₂_C, RingHom.id_apply, sub_eq_zero] using hl
  have hd (i : TubeSource.Coordinate bits) :
      (pderiv i (TubeSource.polynomial bits s)).eval₂ (TubeRegularFiber.coefficientMap bits φ)
        (fun k => z (some k)) = aeval (fun k => z (some k)) (pderiv i p) := by
    rw [← TubeRegularFiber.eval_specialized_partial, hpoly]
    simp only [map_sub, MvPolynomial.pderiv_C, sub_zero, MvPolynomial.pderiv_map,
      aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_map, RingHom.id_comp]
  have hc (i : TubeSource.Coordinate bits) :
      aeval (fun k => z (some k)) (pderiv i p) =
        TubeRegularFiber.direction bits φ i *
          aeval (fun k => z (some k)) (pderiv (TubePolynomial.base _) p) := by
    by_cases hi : i = TubePolynomial.base _
    · rw [hi, hb, one_mul]
    · have h := hr.1.1 (some ⟨i, hi⟩)
      change (TubeSource.integerProjection bits s (some ⟨i, hi⟩)).eval₂ (Int.castRingHom L)
        (TubeMacaulay.values (TubeIndexed.arity bits) φ (fun k => z (some k))) = 0 at h
      rw [TubeRegularFiber.eval_partial] at h
      have hh := sub_eq_zero.mp h
      exact (hd i).symm.trans (hh.trans (congrArg
        (fun t => TubeRegularFiber.direction bits φ i * t) (hd (TubePolynomial.base _))))
  have hu : z none * aeval (fun k => z (some k)) (pderiv (TubePolynomial.base _) p) = 1 := by
    have h := hz none
    change (ReciprocalEquation.polynomial _ _).eval₂ _
      (fun i => i.elim (z none) (TubeMacaulay.values _ φ (fun k => z (some k)))) = 0 at h
    rw [ReciprocalEquation.eval] at h
    change z none * (pderiv (TubeRegularSource.base (TubeIndexed.arity bits))
      (TubeSource.integerProjection bits s none)).eval₂ (Int.castRingHom L)
        (TubeMacaulay.values _ φ (fun k => z (some k))) - 1 = 0 at h
    rw [TubeRegularFiber.eval_base_derivative] at h
    exact (congrArg (fun t => z none * t) (hd (TubePolynomial.base _))).symm.trans
      (sub_eq_zero.mp h)
  rw [eval_determinant, hpoly, extended_constShift]
  exact GenericProjectionJacobian.extended_det_ne_zero p (TubePolynomial.base _) alpha
    (TubeRegularFiber.direction bits φ) (fun k => z (some k)) (z none) hind hp hc hu
end IndependentLevel

end LeanCanny.ETR.TubeRegularJacobianGeneric
