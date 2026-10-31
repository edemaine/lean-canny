/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterExtensionMatrix
public import LeanCanny.Algebra.FixedWidthPolynomial

/-! # Bounded monomial bases for integral scalar prefixes

Iterating monic extensions of one degree gives a monomial basis with every
coordinate exponent below that degree. Every algebra element has a bounded
polynomial representative; its coefficients are regular-representation
matrix entries at the column denoting one.
-/

@[expose] public section
namespace LeanCanny.Algebra
open scoped Classical BigOperators

structure IntegralCoordinateBasis (A : Type*) [CommRing A] (m N : ℕ) where
  generator : Fin m → A
  basis : Module.Basis (Fin m → Fin N) ℤ A
  basis_apply : ∀ e, basis e = ∏ i, generator i ^ (e i).val

namespace IntegralCoordinateBasis
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {m N : ℕ}

noncomputable def base (N : ℕ) : IntegralCoordinateBasis ℤ 0 N where
  generator := Fin.elim0
  basis := Module.Basis.singleton (Fin 0 → Fin N) ℤ
  basis_apply e := by simp

def indexEquiv (m N : ℕ) : ((Fin m → Fin N) × Fin N) ≃ (Fin (m + 1) → Fin N) where
  toFun e := Fin.cons e.2 e.1
  invFun e := (fun i => e i.succ, e 0)
  left_inv e := by cases e; rfl
  right_inv e := by ext i; exact Fin.cases rfl (fun _ => rfl) i

noncomputable def relativeBasis [Nontrivial A] (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) :
    Module.Basis (Fin N) A (AdjoinRoot p) :=
  (AdjoinRoot.powerBasis' hp).basis.reindex (finCongr hdeg)

theorem relativeBasis_apply [Nontrivial A] (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) (i : Fin N) :
    relativeBasis p hp hdeg i = AdjoinRoot.root p ^ i.val := by
  simp only [relativeBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

noncomputable def step [Nontrivial A] (b : IntegralCoordinateBasis A m N)
    (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) : IntegralCoordinateBasis (AdjoinRoot p) (m + 1) N where
  generator := Fin.cons (AdjoinRoot.root p) (fun i => AdjoinRoot.of p (b.generator i))
  basis := (b.basis.smulTower (relativeBasis p hp hdeg)).reindex (indexEquiv m N)
  basis_apply e := by
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply]
    change b.basis (fun i => e i.succ) • relativeBasis p hp hdeg (e 0) = _
    rw [b.basis_apply, relativeBasis_apply, Algebra.smul_def]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change AdjoinRoot.of p (∏ i, b.generator i ^ (e i.succ).val) * AdjoinRoot.root p ^ (e 0).val = _
    rw [map_prod]
    simp only [map_pow]
    exact mul_comm _ _

noncomputable def exponent (e : Fin m → Fin N) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (e i).val)

theorem exponent_injective : Function.Injective (exponent (m := m) (N := N)) := by
  intro e f h
  funext i
  apply Fin.ext
  exact congrArg (fun v : Fin m →₀ ℕ => v i) h

noncomputable def representative (b : IntegralCoordinateBasis A m N) (a : A) : MvPolynomial (Fin m) ℤ :=
  ∑ e : Fin m → Fin N, monomial (exponent e) (b.basis.repr a e)

theorem representative_coefficient (b : IntegralCoordinateBasis A m N) (a : A) (e : Fin m → Fin N) :
    (b.representative a).coeff (exponent e) = b.basis.repr a e := by
  rw [representative, coeff_sum, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    rw [coeff_monomial, ite_eq_right (fun h => hfe (exponent_injective h))]
  · simp

theorem representative_support (b : IntegralCoordinateBasis A m N) (a : A)
    (v : Fin m →₀ ℕ) (hv : v ∈ (b.representative a).support) (i : Fin m) : v i < N := by
  have HC := MvPolynomial.mem_support_iff.mp hv
  by_contra hi
  apply HC
  rw [representative, coeff_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [coeff_monomial]
  apply ite_eq_right
  intro H
  have HE : v i < N := by rw [← H]; exact (e i).isLt
  exact hi HE

theorem representative_degree (b : IntegralCoordinateBasis A m N) (a : A) :
    (b.representative a).totalDegree ≤ m * (N - 1) := by
  rw [representative]
  apply totalDegree_finsetSum_le
  intro e _
  apply (totalDegree_monomial_le _ _).trans
  change (exponent e).degree ≤ _
  rw [Finsupp.degree_eq_sum]
  calc
    _ ≤ Finset.univ.sum (fun _i : Fin m => N - 1) := Finset.sum_le_sum (fun i _ => by have := (e i).isLt; change (e i).val ≤ _; omega)
    _ = m * (N - 1) := by simp

theorem representative_eval (b : IntegralCoordinateBasis A m N) (a : A) :
    (b.representative a).aeval b.generator = a := by
  rw [representative, map_sum]
  have HE (e : Fin m → Fin N) :
      (monomial (exponent e) (b.basis.repr a e)).aeval b.generator = (b.basis.repr a e) • b.basis e := by
    rw [MvPolynomial.aeval_def, eval₂_monomial]
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [exponent, Finsupp.coe_equivFunOnFinite_symm, Algebra.smul_def, b.basis_apply]
  simp only [HE]
  exact b.basis.sum_repr a

def zeroIndex (m N : ℕ) (hN : 0 < N) : Fin m → Fin N := fun _ => ⟨0, hN⟩

theorem basis_zero (b : IntegralCoordinateBasis A m N) (hN : 0 < N) : b.basis (zeroIndex m N hN) = 1 := by
  rw [b.basis_apply]
  simp [zeroIndex]

theorem coefficient_matrix (b : IntegralCoordinateBasis A m N) (hN : 0 < N) (a : A) (e : Fin m → Fin N) :
    (b.representative a).coeff (exponent e) = Algebra.leftMulMatrix b.basis a e (zeroIndex m N hN) := by
  rw [representative_coefficient, Algebra.leftMulMatrix_eq_repr_mul, basis_zero b hN, mul_one]

end IntegralCoordinateBasis
end LeanCanny.Algebra
