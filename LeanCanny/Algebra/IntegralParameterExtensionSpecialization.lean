/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralParameterExtensionMatrix
/-! # Actual fixed-degree scalar extension maps under coefficient specialization

The advertised degree is fixed. Monic normalization already commutes with
any coefficient homomorphism, so its actual quotient and relative power
basis specialize without requiring a surviving selected coefficient.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterExtension
open Polynomial
variable {A B :Type*} [CommRing A] [CommRing B]

/-- The actual quotient homomorphism, not a supplied correspondence of tables. -/
noncomputable def specialize (φ :A→+*B) (p :A[X]) (d :ℕ) :
    Extension p d→+*Extension (p.map φ) d:=
  AdjoinRoot.map φ _ _ (by rw [FixedDegreeIntegralNormalization.map])

theorem specialize_of (φ :A→+*B) (p :A[X]) (d :ℕ) (a :A) :
    specialize φ p d (AdjoinRoot.of _ a)=AdjoinRoot.of _ (φ a):=
  AdjoinRoot.map_of _ _ _ _ _

theorem specialize_root (φ :A→+*B) (p :A[X]) (d :ℕ) :
    specialize φ p d (AdjoinRoot.root _)=AdjoinRoot.root _:=
  AdjoinRoot.map_root _ _ _ _

theorem specialize_mk (φ :A→+*B) (p q :A[X]) (d :ℕ) :
    specialize φ p d (AdjoinRoot.mk _ q)=AdjoinRoot.mk _ (q.map φ):=by
  have HE :(specialize φ p d).comp (AdjoinRoot.mk _) =
      (AdjoinRoot.mk _).comp (Polynomial.mapRingHom φ):=by
    apply Polynomial.ringHom_ext
    · intro a
      change specialize φ p d (AdjoinRoot.mk _ (C a))=AdjoinRoot.mk _ ((C a).map φ)
      rw [map_C,AdjoinRoot.mk_C,AdjoinRoot.mk_C,specialize_of]
    · change specialize φ p d (AdjoinRoot.root _)=AdjoinRoot.mk _ (X.map φ)
      rw [map_X,AdjoinRoot.mk_X,specialize_root]
  exact RingHom.congr_fun HE q

theorem specialize_monomial (φ :A→+*B) (p :A[X]) (d k :ℕ) (a :A) :
    specialize φ p d (AdjoinRoot.mk _ (monomial k a))=
      AdjoinRoot.mk _ (monomial k (φ a)):=by
  rw [specialize_mk,map_monomial]

section Basis
variable [Nontrivial A] [Nontrivial B]

theorem specialize_relativeBasis (φ :A→+*B) (p :A[X]) (d :ℕ) (i :Fin d) :
    specialize φ p d (relativeBasis p d i)=relativeBasis (p.map φ) d i:=by
  rw [relativeBasis_apply,map_pow,specialize_root,relativeBasis_apply]

/-- Relative coordinates are specialized in the coefficient ring. Neither
base ring is assumed finite free over the integers. -/
theorem relativeBasis_repr_specialize (φ :A→+*B) (p :A[X]) (d :ℕ)
    (a :Extension p d) (i :Fin d) :
    (relativeBasis (p.map φ) d).repr (specialize φ p d a) i=
      φ ((relativeBasis p d).repr a i):=by
  induction a using AdjoinRoot.induction_on with
  | ih q=>
    rw [specialize_mk,relativeBasis_repr_mk,relativeBasis_repr_mk]
    rw [←Polynomial.coeff_map,Polynomial.map_modByMonic φ (FixedDegreeIntegralNormalization.monic p d),
      FixedDegreeIntegralNormalization.map]

end Basis

section Algebras
variable {R :Type*} [CommRing R] [Algebra R A] [Algebra R B]

noncomputable def specializeAlgHom (φ :A→ₐ[R]B) (p :A[X]) (d :ℕ) :
    Extension p d→ₐ[R]Extension (p.map φ.toRingHom) d where
  __:=specialize φ.toRingHom p d
  commutes' r:=by
    change specialize φ.toRingHom p d (AdjoinRoot.of _ (algebraMap R A r))=
      AdjoinRoot.of _ (algebraMap R B r)
    rw [specialize_of]
    exact congrArg (AdjoinRoot.of _) (φ.commutes r)

theorem specializeAlgHom_apply (φ :A→ₐ[R]B) (p :A[X]) (d :ℕ) (a :Extension p d) :
    specializeAlgHom φ p d a=specialize φ.toRingHom p d a:=rfl

end Algebras
end LeanCanny.Algebra.IntegralParameterExtension
