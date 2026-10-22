/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LevelProjectionSpecialization
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Generic projection-critical roots have invertible Jacobians

Differentiate the level and normalized direction coordinates independently.
The resulting coordinate derivatives provide a right inverse of the spatial
critical Jacobian up to a nonzero diagonal factor. Adjoining the reciprocal
of the base partial then gives an invertible full extended Jacobian.
-/

@[expose] public section

namespace LeanCanny.Algebra.GenericProjectionJacobian
open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

noncomputable def spatial (p : MvPolynomial ι K) (base : ι) (v x : ι → L) : Matrix ι ι L :=
  fun i k => if i = base then aeval x (pderiv k p) else
    aeval x (pderiv k (pderiv i p)) - v i * aeval x (pderiv k (pderiv base p))

def parameters (base : ι) (alpha : L) (v : ι → L) : ι → L :=
  fun i => if i = base then alpha else v i

theorem spatial_det_ne_zero [CharZero K] (p : MvPolynomial ι K) (base : ι)
    (alpha : L) (v x : ι → L) (hind : AlgebraicIndependent K (parameters base alpha v))
    (hlevel : aeval x p = alpha)
    (hcritical : ∀ i, aeval x (pderiv i p) = v i * aeval x (pderiv base p))
    (hbase : aeval x (pderiv base p) ≠ 0) : (spatial p base v x).det ≠ 0 := by
  classical
  choose delta hd using fun j => CoordinateDerivation.exists_of_independent hind j
  let M : Matrix ι ι L := fun k j => delta j (x k)
  let w : ι → L := fun i => if i = base then 1 else aeval x (pderiv base p)
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    dsimp [w]
    split_ifs
    · exact one_ne_zero
    · exact hbase
  have halpha (j : ι) : delta j alpha = if base = j then 1 else 0 := by
    simpa only [parameters, ite_true] using hd j base
  have hv (j i : ι) (hi : i ≠ base) : delta j (v i) = if i = j then 1 else 0 := by
    simpa only [parameters, hi, ite_false] using hd j i
  have hproduct : spatial p base v x * M = Matrix.diagonal w := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hi : i = base
    · subst i
      simp only [spatial, ite_true, M, Matrix.diagonal_apply, w, ite_true]
      rw [← CriticalValueAlgebraic.chain_rule, hlevel, halpha]
    · have hdcrit := congrArg (delta j) (hcritical i)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hv j i hi,
        CriticalValueAlgebraic.chain_rule, CriticalValueAlgebraic.chain_rule] at hdcrit
      simp only [spatial, hi, ite_false, M, Matrix.diagonal_apply]
      rw [show (∑ k, (aeval x (pderiv k (pderiv i p)) -
          v i * aeval x (pderiv k (pderiv base p))) * delta j (x k)) =
        (∑ k, aeval x (pderiv k (pderiv i p)) * delta j (x k)) -
          v i * ∑ k, aeval x (pderiv k (pderiv base p)) * delta j (x k) by
            simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]]
      have he : (∑ k, aeval x (pderiv k (pderiv i p)) * delta j (x k)) -
          v i * ∑ k, aeval x (pderiv k (pderiv base p)) * delta j (x k) =
          (if i = j then 1 else 0) * aeval x (pderiv base p) := by
        calc
          _ = aeval x (pderiv base p) * (if i = j then 1 else 0) := by linear_combination hdcrit
          _ = _ := mul_comm _ _
      rw [he]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, one_mul, w, hi, ite_false]
      · simp only [hij, ite_false, zero_mul]
  have hdet : (spatial p base v x * M).det ≠ 0 := by
    rw [hproduct, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  intro hz
  exact hdet (by rw [Matrix.det_mul, hz, zero_mul])

end LeanCanny.Algebra.GenericProjectionJacobian

namespace LeanCanny.Algebra.GenericProjectionJacobian
open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

noncomputable def extended (p : MvPolynomial ι K) (base : ι) (v x : ι → L) (u : L) :
    Matrix (Option ι) (Option ι) L
  | none, none => aeval x (pderiv base p)
  | none, some k => u * aeval x (pderiv k (pderiv base p))
  | some _, none => 0
  | some i, some k => spatial p base v x i k

theorem extended_det (p : MvPolynomial ι K) (base : ι) (v x : ι → L) (u : L) :
    (extended p base v x u).det = (spatial p base v x).det * aeval x (pderiv base p) := by
  let A : Matrix (Sum ι PUnit.{1}) (Sum ι PUnit.{1}) L := Matrix.fromBlocks (spatial p base v x) 0
    (fun _ k => u * aeval x (pderiv k (pderiv base p))) (fun _ _ => aeval x (pderiv base p))
  have he : extended p base v x u = A.submatrix (Equiv.optionEquivSumPUnit ι) (Equiv.optionEquivSumPUnit ι) := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he, Matrix.det_submatrix_equiv_self]
  have hd := Matrix.det_fromBlocks_zero₁₂ (spatial p base v x)
    (fun (_ : PUnit.{1}) k => u * aeval x (pderiv k (pderiv base p)))
    (fun (_ _ : PUnit.{1}) => aeval x (pderiv base p))
  rw [Matrix.det_unique (fun (_ _ : PUnit.{1}) => aeval x (pderiv base p))] at hd
  exact hd

/-- Generic critical equations, including their reciprocal equation, are nonsingular. -/
theorem extended_det_ne_zero [CharZero K] (p : MvPolynomial ι K) (base : ι)
    (alpha : L) (v x : ι → L) (u : L) (hind : AlgebraicIndependent K (parameters base alpha v))
    (hlevel : aeval x p = alpha)
    (hcritical : ∀ i, aeval x (pderiv i p) = v i * aeval x (pderiv base p))
    (hreciprocal : u * aeval x (pderiv base p) = 1) :
    (extended p base v x u).det ≠ 0 := by
  have hb : aeval x (pderiv base p) ≠ 0 := fun h => zero_ne_one (by simpa only [h, mul_zero] using hreciprocal)
  rw [extended_det]
  exact mul_ne_zero (spatial_det_ne_zero p base alpha v x hind hlevel hcritical hb) hb

end LeanCanny.Algebra.GenericProjectionJacobian

namespace LeanCanny.Algebra.GenericProjectionJacobian
open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

noncomputable def equation (p : MvPolynomial ι K) (base : ι) (alpha : L) (v : ι → L) :
    Option ι → MvPolynomial (Option ι) L
  | none => X none * GenericProjectionFinite.liftPolynomial (pderiv base p) - 1
  | some i => if i = base then GenericProjectionFinite.liftPolynomial p - C alpha else
      GenericProjectionFinite.liftPolynomial (pderiv i p) - C (v i) * GenericProjectionFinite.liftPolynomial (pderiv base p)

omit [Fintype ι] in
private theorem pderiv_none_rename {R : Type*} [CommRing R] (p : MvPolynomial ι R) :
    pderiv (none : Option ι) (rename some p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, pderiv_X]

omit [Fintype ι] in
private theorem pderiv_none_lift (p : MvPolynomial ι K) :
    pderiv (none : Option ι) (GenericProjectionFinite.liftPolynomial (B := L) p) = 0 :=
  pderiv_none_rename _

omit [Fintype ι] [DecidableEq ι] in
private theorem eval_pderiv_some_lift (p : MvPolynomial ι K) (k : ι) (x : ι → L) (u : L) :
    aeval (fun i : Option ι => i.elim u x)
      (pderiv (some k) (GenericProjectionFinite.liftPolynomial (B := L) p)) =
        aeval x (pderiv k p) := by
  rw [GenericProjectionFinite.liftPolynomial, pderiv_rename (Option.some_injective ι), pderiv_map]
  exact GenericProjectionFinite.eval_liftPolynomial _ _

omit [Fintype ι] in
theorem formalJacobian_eq (p : MvPolynomial ι K) (base : ι) (alpha : L) (v x : ι → L) (u : L) :
    (fun i j => aeval (fun k : Option ι => k.elim u x) (pderiv j (equation p base alpha v i))) =
      extended p base v x u := by
  ext i j
  cases i with
  | none =>
    cases j with
    | none =>
      simp only [equation, map_sub, pderiv_mul, pderiv_X_self, pderiv_one,
        pderiv_none_lift, mul_zero, add_zero, sub_zero, one_mul,
        GenericProjectionFinite.eval_liftPolynomial, Option.elim_some, extended]
    | some k =>
      have hne : (none : Option ι) ≠ some k := by intro h; cases h
      simp only [equation, map_sub, pderiv_mul, pderiv_X, Pi.single_apply,
        hne, ite_false, pderiv_one, zero_mul,
        zero_add, sub_zero, map_mul, aeval_X, Option.elim_none,
        eval_pderiv_some_lift, extended]
  | some i =>
    by_cases hi : i = base
    · subst i
      cases j with
      | none => simp only [equation, ite_true, map_sub, pderiv_none_lift,
          pderiv_C, sub_zero, map_zero, extended]
      | some k => simp only [equation, ite_true, map_sub, pderiv_C,
          sub_zero, eval_pderiv_some_lift, extended, spatial, ite_true]
    · cases j with
      | none => simp only [equation, hi, ite_false, map_sub, pderiv_mul,
          pderiv_none_lift, pderiv_C, zero_mul, mul_zero, add_zero, sub_zero, map_zero, extended]
      | some k => simp only [equation, hi, ite_false, map_sub, pderiv_mul, pderiv_C,
          zero_mul, zero_add, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
          eval_pderiv_some_lift, extended, spatial]

theorem formalJacobian_det_ne_zero [CharZero K] (p : MvPolynomial ι K) (base : ι)
    (alpha : L) (v x : ι → L) (u : L) (hind : AlgebraicIndependent K (parameters base alpha v))
    (hlevel : aeval x p = alpha)
    (hcritical : ∀ i, aeval x (pderiv i p) = v i * aeval x (pderiv base p))
    (hreciprocal : u * aeval x (pderiv base p) = 1) :
    (Matrix.of fun i j => aeval (fun k : Option ι => k.elim u x)
      (pderiv j (equation p base alpha v i))).det ≠ 0 := by
  change Matrix.det (fun i j => aeval (fun k : Option ι => k.elim u x)
    (pderiv j (equation p base alpha v i))) ≠ 0
  rw [formalJacobian_eq]
  exact extended_det_ne_zero p base alpha v x u hind hlevel hcritical hreciprocal

end LeanCanny.Algebra.GenericProjectionJacobian

namespace LeanCanny.Algebra.GenericProjectionJacobian
open MvPolynomial
open LevelProjectionSpecialization
open scoped Classical
attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem generic_parameters_independent (base : ι) :
    AlgebraicIndependent K (parameters base (genericLevel (K := K) base) (genericDirection (K := K) base)) := by
  let A := ParameterRing K base
  let F := ParameterField K base
  let w : Option (ProjectionFiniteSpecialization.DirectionIndex base) → F := fun i => algebraMap A F (X i)
  have hinj : Function.Injective (IsScalarTower.toAlgHom K A F) := IsFractionRing.injective A F
  have hw : AlgebraicIndependent K w := by
    have h := (MvPolynomial.algebraicIndependent_X
      (Option (ProjectionFiniteSpecialization.DirectionIndex base)) K).map hinj.injOn
    exact h
  have he : parameters base (genericLevel (K := K) base) (genericDirection (K := K) base) =
      w ∘ (Equiv.optionSubtypeNe base).symm := by
    funext i
    by_cases hi : i = base
    · subst i
      simp only [parameters, ite_true, Function.comp_apply, Equiv.optionSubtypeNe_symm_self]
      rfl
    · simp only [parameters, hi, ite_false, Function.comp_apply, Equiv.optionSubtypeNe_symm_of_ne hi]
      simp only [genericDirection, parameterDirection, hi, dite_false]
      rfl
  rw [he]
  exact hw.comp _ (Equiv.optionSubtypeNe base).symm.injective

variable {L : Type*} [Field L] [Algebra K L]

omit [Fintype ι] [DecidableEq ι] in
private theorem eval_map_tower {B : Type*} [Field B] [Algebra K B] [Algebra B L] [IsScalarTower K B L]
    (p : MvPolynomial ι K) (x : ι → L) :
    aeval x (p.map (algebraMap K B)) = aeval x p := by
  simp only [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K B L]

/-- The actual symbolic level/direction system has no singular extended roots
in any field extension of its generic parameter field. -/
theorem generic_extended_det_ne_zero [CharZero K] (p : MvPolynomial ι K) (base : ι)
    [Algebra (ParameterField K base) L] [IsScalarTower K (ParameterField K base) L]
    (z : Option ι → L)
    (hz : ∀ j, aeval z (GenericProjectionFinite.equation
      (levelPolynomial p (genericLevel (K := K) base)) base (genericDirection (K := K) base) j) = 0) :
    (extended p base (fun i => algebraMap (ParameterField K base) L (genericDirection (K := K) base i))
      (fun i => z (some i)) (z none)).det ≠ 0 := by
  let F := ParameterField K base
  let x : ι → L := fun i => z (some i)
  let a : L := algebraMap F L (genericLevel (K := K) base)
  let v : ι → L := fun i => algebraMap F L (genericDirection (K := K) base i)
  have hind : AlgebraicIndependent K (parameters base a v) := by
    have hinj : Function.Injective (IsScalarTower.toAlgHom K F L) := (algebraMap F L).injective
    have h := (generic_parameters_independent (K := K) base).map hinj.injOn
    convert h using 1
    funext i
    by_cases hi : i = base <;> simp [parameters, hi, a, v] <;> rfl
  have heval : aeval x (levelPolynomial p (genericLevel (K := K) base)) = aeval x p - a := by
    rw [levelPolynomial, map_sub, eval_map_tower, aeval_C]
  have hpartial (i : ι) : aeval x (pderiv i (levelPolynomial p (genericLevel (K := K) base))) =
      aeval x (pderiv i p) := by
    rw [pderiv_levelPolynomial, eval_map_tower]
  have hp : aeval x p = a := by
    have h := hz (.inl false)
    rw [GenericProjectionFinite.equation, GenericProjectionFinite.eval_liftPolynomial, heval] at h
    exact sub_eq_zero.mp h
  have hr : z none * aeval x (pderiv base p) = 1 := by
    have h := hz (.inl true)
    rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_X,
      GenericProjectionFinite.eval_liftPolynomial, hpartial, map_one] at h
    exact sub_eq_zero.mp h
  have hc : ∀ i, aeval x (pderiv i p) = v i * aeval x (pderiv base p) := by
    intro i
    have h := hz (.inr i)
    rw [GenericProjectionFinite.equation, map_sub, map_mul, aeval_C,
      GenericProjectionFinite.eval_liftPolynomial, GenericProjectionFinite.eval_liftPolynomial,
      hpartial, hpartial] at h
    exact sub_eq_zero.mp h
  exact extended_det_ne_zero p base a v x (z none) hind hp hc hr

end LeanCanny.Algebra.GenericProjectionJacobian

namespace LeanCanny.Algebra.GenericProjectionJacobian
open MvPolynomial LevelProjectionSpecialization

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

/-- Nonsingularity is stated for the actual formal derivative matrix of the
square reciprocal/level/partial system, rather than an assumed smooth model. -/
theorem generic_formalJacobian_det_ne_zero [CharZero K] (p : MvPolynomial ι K) (base : ι)
    [Algebra (ParameterField K base) L] [IsScalarTower K (ParameterField K base) L]
    (z : Option ι → L)
    (hz : ∀ j, aeval z (GenericProjectionFinite.equation
      (levelPolynomial p (genericLevel (K := K) base)) base (genericDirection (K := K) base) j) = 0) :
    Matrix.det (fun i j => aeval z (pderiv j (equation p base
      (algebraMap (ParameterField K base) L (genericLevel (K := K) base))
      (fun i => algebraMap (ParameterField K base) L (genericDirection (K := K) base i)) i))) ≠ 0 := by
  have he : (fun k : Option ι => k.elim (z none) (fun i => z (some i))) = z := by
    funext k
    cases k <;> rfl
  have h := formalJacobian_eq p base
    (algebraMap (ParameterField K base) L (genericLevel (K := K) base))
    (fun i => algebraMap (ParameterField K base) L (genericDirection (K := K) base i))
    (fun i => z (some i)) (z none)
  rw [he] at h
  rw [h]
  exact generic_extended_det_ne_zero p base z hz

end LeanCanny.Algebra.GenericProjectionJacobian
