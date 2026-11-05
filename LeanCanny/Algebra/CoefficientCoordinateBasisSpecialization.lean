/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCoordinateBasis
public import LeanCanny.Algebra.PaddedIntegralParameterExtensionSpecialization
/-! # Semilinear specialization of actual bounded monomial coordinates

Only coefficient compatibility and generator images form the parent invariant.
Basis vectors and every coordinate are derived from the actual monomials.
The base and padded quotient step construct that invariant themselves.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientCoordinateBasis
open scoped Classical BigOperators
variable {R S A B :Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] {m N :ℕ}

structure Specializes (φ :R→+*S) (ψ :A→+*B)
    (b :CoefficientCoordinateBasis R A m N) (c :CoefficientCoordinateBasis S B m N) :Prop where
  coefficients :∀r,ψ (algebraMap R A r)=algebraMap S B (φ r)
  generators :∀i,ψ (b.generator i)=c.generator i

namespace Specializes
variable {φ :R→+*S} {ψ :A→+*B} {b :CoefficientCoordinateBasis R A m N}
  {c :CoefficientCoordinateBasis S B m N} (H :Specializes φ ψ b c)
include H

theorem smul (r :R) (a :A) :ψ (r • a)=φ r • ψ a:=by
  simp only [Algebra.smul_def,map_mul,H.coefficients]

theorem basis (e :Fin m→Fin N) :ψ (b.basis e)=c.basis e:=by
  rw [b.basis_apply,c.basis_apply,map_prod]
  simp only [map_pow,H.generators]

/-- All coordinate transport follows from the constructed monomial bases. -/
theorem coordinates (a :A) (e :Fin m→Fin N) :
    c.basis.repr (ψ a) e=φ (b.basis.repr a e):=by
  have HE :ψ a=∑j,φ (b.basis.repr a j) • c.basis j:=by
    calc
      ψ a=ψ (∑j,b.basis.repr a j • b.basis j):=congrArg ψ (b.basis.sum_repr a).symm
      _=∑j,ψ (b.basis.repr a j • b.basis j):=map_sum ψ _ _
      _=∑j,φ (b.basis.repr a j) • c.basis j:=by
        apply Finset.sum_congr rfl
        intro j _
        rw [H.smul,H.basis]
  rw [HE,Module.Basis.repr_sum_self]

theorem representative_map (a :A) :
    MvPolynomial.map φ (b.representative a)=c.representative (ψ a):=by
  rw [representative,representative,map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [MvPolynomial.map_monomial,H.coordinates]

theorem polynomial_map (p :Polynomial A) :
    (b.polynomial p).map (MvPolynomial.map φ)=c.polynomial (p.map ψ):=by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map,polynomial_coefficient,polynomial_coefficient,Polynomial.coeff_map]
  exact H.representative_map _

/-- The next map is the actual padded quotient homomorphism; no new basis
or matrix compatibility premise is supplied at the extension. -/
theorem paddedStep [Nontrivial A] [Nontrivial B] (p :Polynomial A) (d :ℕ) :
    Specializes φ (PaddedIntegralParameterExtension.specialize ψ p d N)
      (b.paddedStep p d) (c.paddedStep (p.map ψ) d):=by
  constructor
  · intro r
    change PaddedIntegralParameterExtension.specialize ψ p d N
        (AdjoinRoot.of _ (algebraMap R A r))=AdjoinRoot.of _ (algebraMap S B (φ r))
    rw [PaddedIntegralParameterExtension.specialize_of,H.coefficients]
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · change PaddedIntegralParameterExtension.specialize ψ p d N
        (AdjoinRoot.root _)=AdjoinRoot.root _
      exact PaddedIntegralParameterExtension.specialize_root ψ p d N
    · change PaddedIntegralParameterExtension.specialize ψ p d N
        (AdjoinRoot.of _ (b.generator j))=AdjoinRoot.of _ (c.generator j)
      rw [PaddedIntegralParameterExtension.specialize_of,H.generators]

end Specializes

theorem base_specializes (φ :R→+*S) (N :ℕ) :Specializes φ φ (base R N) (base S N):=by
  constructor
  · intro r
    simp only [Algebra.algebraMap_self,RingHom.id_apply]
  · intro i
    exact Fin.elim0 i

end LeanCanny.Algebra.CoefficientCoordinateBasis
