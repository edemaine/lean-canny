/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCoordinatePolynomial
public import LeanCanny.Algebra.PaddedIntegralParameterExtension
/-! # Bounded monomial coordinates over an arbitrary coefficient ring -/
@[expose] public section
namespace LeanCanny.Algebra
open scoped Classical BigOperators

structure CoefficientCoordinateBasis (R A :Type*) [CommRing R] [CommRing A] [Algebra R A] (m N :ℕ) where
  generator :Fin m→A
  basis :Module.Basis (Fin m→Fin N) R A
  basis_apply :∀e,basis e=∏i,generator i^(e i).val

namespace CoefficientCoordinateBasis
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {m N : ℕ}

noncomputable def base (R :Type*) [CommRing R] (N : ℕ) : CoefficientCoordinateBasis R R 0 N where
  generator := Fin.elim0
  basis := Module.Basis.singleton (Fin 0 → Fin N) R
  basis_apply e := by simp

abbrev indexEquiv:=IntegralCoordinateBasis.indexEquiv

noncomputable abbrev relativeBasis [Nontrivial A] (p :Polynomial A) (hp :p.Monic) (hdeg :p.natDegree=N) :=
  IntegralCoordinateBasis.relativeBasis p hp hdeg

theorem relativeBasis_apply [Nontrivial A] (p :Polynomial A) (hp :p.Monic) (hdeg :p.natDegree=N) (i :Fin N) :
    relativeBasis p hp hdeg i=AdjoinRoot.root p^i.val:=
  IntegralCoordinateBasis.relativeBasis_apply p hp hdeg i

noncomputable def step [Nontrivial A] (b : CoefficientCoordinateBasis R A m N)
    (p : Polynomial A) (hp : p.Monic) (hdeg : p.natDegree = N) : CoefficientCoordinateBasis R (AdjoinRoot p) (m + 1) N where
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

noncomputable abbrev exponent (e :Fin m→Fin N) :Fin m→₀ℕ:=IntegralCoordinateBasis.exponent e

theorem exponent_injective :Function.Injective (exponent (m:=m) (N:=N)):=
  IntegralCoordinateBasis.exponent_injective

noncomputable def representative (b : CoefficientCoordinateBasis R A m N) (a : A) : MvPolynomial (Fin m) R :=
  ∑ e : Fin m → Fin N, monomial (exponent e) (b.basis.repr a e)

theorem representative_coefficient (b : CoefficientCoordinateBasis R A m N) (a : A) (e : Fin m → Fin N) :
    (b.representative a).coeff (exponent e) = b.basis.repr a e := by
  rw [representative, coeff_sum, Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    rw [coeff_monomial, ite_eq_right (fun h => hfe (exponent_injective h))]
  · simp

theorem representative_support (b : CoefficientCoordinateBasis R A m N) (a : A)
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

theorem representative_degree (b : CoefficientCoordinateBasis R A m N) (a : A) :
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

theorem representative_eval (b : CoefficientCoordinateBasis R A m N) (a : A) :
    (b.representative a).aeval b.generator = a := by
  rw [representative, map_sum]
  have HE (e : Fin m → Fin N) :
      (monomial (exponent e) (b.basis.repr a e)).aeval b.generator = (b.basis.repr a e) • b.basis e := by
    rw [MvPolynomial.aeval_def, eval₂_monomial]
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [exponent, IntegralCoordinateBasis.exponent, Finsupp.coe_equivFunOnFinite_symm, Algebra.smul_def, b.basis_apply]
  simp only [HE]
  exact b.basis.sum_repr a

def zeroIndex (m N : ℕ) (hN : 0 < N) : Fin m → Fin N := fun _ => ⟨0, hN⟩

theorem basis_zero (b : CoefficientCoordinateBasis R A m N) (hN : 0 < N) : b.basis (zeroIndex m N hN) = 1 := by
  rw [b.basis_apply]
  simp [zeroIndex]

theorem coefficient_matrix (b : CoefficientCoordinateBasis R A m N) (hN : 0 < N) (a : A) (e : Fin m → Fin N) :
    (b.representative a).coeff (exponent e) = Algebra.leftMulMatrix b.basis a e (zeroIndex m N hN) := by
  rw [representative_coefficient, Algebra.leftMulMatrix_eq_repr_mul, basis_zero b hN, mul_one]

theorem representative_zero (b : CoefficientCoordinateBasis R A m N) : b.representative 0 = 0 := by
  simp [representative]

theorem representative_one (b : CoefficientCoordinateBasis R A m N) (hN : 0 < N) :
    b.representative 1 = 1 := by
  have HR : b.basis.repr 1 = Finsupp.single (zeroIndex m N hN) 1 := by
    rw [← b.basis_zero hN, Module.Basis.repr_self]
  rw [representative, HR, Finset.sum_eq_single (zeroIndex m N hN)]
  · have HZ : exponent (zeroIndex m N hN) = 0 := by ext i; rfl
    rw [Finsupp.single_eq_same, HZ, monomial_zero', map_one]
  · intro e _ he
    simp [Finsupp.single_eq_of_ne he]
  · simp

noncomputable def polynomial (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) :
    Polynomial (MvPolynomial (Fin m) R) :=
  ∑ i ∈ p.support, Polynomial.monomial i (b.representative (p.coeff i))

theorem polynomial_coefficient (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) (i : ℕ) :
    (b.polynomial p).coeff i = b.representative (p.coeff i) := by
  rw [polynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq']
  by_cases hi : i ∈ p.support
  · rw [ite_eq_left hi]
  · rw [ite_eq_right hi, Polynomial.notMem_support_iff.mp hi, representative_zero]

theorem polynomial_coefficient_degree (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) (i : ℕ) :
    ((b.polynomial p).coeff i).totalDegree ≤ m * (N - 1) := by
  rw [polynomial_coefficient]
  exact b.representative_degree _

theorem polynomial_map (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) :
    (b.polynomial p).map (MvPolynomial.aeval b.generator).toRingHom = p := by
  ext i
  rw [Polynomial.coeff_map, polynomial_coefficient]
  exact b.representative_eval _

theorem polynomial_eval {K : Type*} [CommRing K] [Algebra R K] (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A)
    (φ : A →ₐ[R] K) (x : K) :
    (b.polynomial p).eval₂ (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom x = p.eval₂ φ.toRingHom x := by
  have HM : (b.polynomial p).map (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom = p.map φ.toRingHom := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, polynomial_coefficient]
    have HE := MvPolynomial.comp_aeval_apply (φ := φ) (p := b.representative (p.coeff i)) (f := b.generator)
    rw [b.representative_eval] at HE
    exact HE.symm
  have H := congrArg (fun q : Polynomial K => q.eval x) HM
  simpa only [Polynomial.eval_map] using H

theorem polynomial_monic [Nontrivial R] [Nontrivial A] (b : CoefficientCoordinateBasis R A m N) (hN : 0 < N)
    (p : Polynomial A) (hp : p.Monic) : (b.polynomial p).Monic ∧ (b.polynomial p).natDegree = p.natDegree := by
  have HD : (b.polynomial p).natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [polynomial_coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt hi, representative_zero]
  have HT : (b.polynomial p).coeff p.natDegree = 1 := by
    rw [polynomial_coefficient, Polynomial.coeff_natDegree, hp.leadingCoeff, representative_one b hN]
  have HE : (b.polynomial p).natDegree = p.natDegree := Nat.le_antisymm HD (Polynomial.le_natDegree_of_ne_zero (by rw [HT]; exact one_ne_zero))
  refine ⟨?_, HE⟩
  rw [Polynomial.Monic, Polynomial.leadingCoeff, HE, HT]

noncomputable def paddedStep [Nontrivial A] (b :CoefficientCoordinateBasis R A m N)
    (p :Polynomial A) (d :ℕ) :CoefficientCoordinateBasis R
      (PaddedIntegralParameterExtension.Extension p d N) (m+1) N:=
  b.step (PaddedIntegralNormalization.polynomial p d N)
    (PaddedIntegralNormalization.monic p d N) (PaddedIntegralNormalization.natDegree p d N)

noncomputable def ofIntegral (b :IntegralCoordinateBasis A m N) :CoefficientCoordinateBasis ℤ A m N where
  generator:=b.generator
  basis:=b.basis
  basis_apply:=b.basis_apply

noncomputable def toIntegral (b :CoefficientCoordinateBasis ℤ A m N) :IntegralCoordinateBasis A m N where
  generator:=b.generator
  basis:=b.basis
  basis_apply:=b.basis_apply

theorem toIntegral_ofIntegral (b :IntegralCoordinateBasis A m N) :(ofIntegral b).toIntegral=b:=rfl

theorem ofIntegral_base (N :ℕ) :ofIntegral (IntegralCoordinateBasis.base N)=base ℤ N:=rfl

theorem ofIntegral_step [Nontrivial A] (b :IntegralCoordinateBasis A m N)
    (p :Polynomial A) (hp :p.Monic) (hd :p.natDegree=N) :
    ofIntegral (b.step p hp hd)=(ofIntegral b).step p hp hd:=rfl

theorem ofIntegral_representative (b :IntegralCoordinateBasis A m N) (a :A) :
    (ofIntegral b).representative a=b.representative a:=rfl

theorem ofIntegral_polynomial (b :IntegralCoordinateBasis A m N) (p :Polynomial A) :
    (ofIntegral b).polynomial p=b.polynomial p:=rfl

theorem ofIntegral_paddedStep [Nontrivial A] (b :IntegralCoordinateBasis A m N) (p :Polynomial A) (d :ℕ) :
    ofIntegral (PaddedIntegralParameterExtension.coordinateBasis b p d)=(ofIntegral b).paddedStep p d:=rfl

end CoefficientCoordinateBasis
end LeanCanny.Algebra
