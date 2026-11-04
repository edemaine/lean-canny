/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralParameterExtensionSpecialization
public import LeanCanny.Algebra.PaddedIntegralParameterExtension
/-! # Actual uniform-rank scalar extensions under coefficient specialization

Both valid and out-of-range advertised degrees use their literal padded
normalization. Coordinates are relative to the coefficient rings, with no
assumption of a finite integer basis for a symbolic parameter algebra.
-/
@[expose] public section
namespace LeanCanny.Algebra
open Polynomial
variable {A B :Type*} [CommRing A] [CommRing B]

namespace PaddedIntegralNormalization

theorem map (φ :A→+*B) (p :A[X]) (d N :ℕ) :
    (polynomial p d N).map φ=polynomial (p.map φ) d N:=by
  unfold polynomial
  split_ifs <;> simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,
    FixedDegreeIntegralNormalization.map]

end PaddedIntegralNormalization
namespace PaddedIntegralParameterExtension

noncomputable def specialize (φ :A→+*B) (p :A[X]) (d N :ℕ) :
    Extension p d N→+*Extension (p.map φ) d N:=
  AdjoinRoot.map φ _ _ (by rw [PaddedIntegralNormalization.map])

theorem specialize_of (φ :A→+*B) (p :A[X]) (d N :ℕ) (a :A) :
    specialize φ p d N (AdjoinRoot.of _ a)=AdjoinRoot.of _ (φ a):=
  AdjoinRoot.map_of _ _ _ _ _

theorem specialize_root (φ :A→+*B) (p :A[X]) (d N :ℕ) :
    specialize φ p d N (AdjoinRoot.root _)=AdjoinRoot.root _:=
  AdjoinRoot.map_root _ _ _ _

theorem specialize_mk (φ :A→+*B) (p q :A[X]) (d N :ℕ) :
    specialize φ p d N (AdjoinRoot.mk _ q)=AdjoinRoot.mk _ (q.map φ):=by
  have HE :(specialize φ p d N).comp (AdjoinRoot.mk _) =
      (AdjoinRoot.mk _).comp (Polynomial.mapRingHom φ):=by
    apply Polynomial.ringHom_ext
    · intro a
      change specialize φ p d N (AdjoinRoot.mk _ (C a))=AdjoinRoot.mk _ ((C a).map φ)
      rw [map_C,AdjoinRoot.mk_C,AdjoinRoot.mk_C,specialize_of]
    · change specialize φ p d N (AdjoinRoot.root _)=AdjoinRoot.mk _ (X.map φ)
      rw [map_X,AdjoinRoot.mk_X,specialize_root]
  exact RingHom.congr_fun HE q

theorem specialize_monomial (φ :A→+*B) (p :A[X]) (d N k :ℕ) (a :A) :
    specialize φ p d N (AdjoinRoot.mk _ (monomial k a))=
      AdjoinRoot.mk _ (monomial k (φ a)):=by
  rw [specialize_mk,map_monomial]

section Basis
variable [Nontrivial A] [Nontrivial B]

noncomputable def relativeBasis (p :A[X]) (d N :ℕ) :Module.Basis (Fin N) A (Extension p d N):=
  IntegralCoordinateBasis.relativeBasis (PaddedIntegralNormalization.polynomial p d N)
    (PaddedIntegralNormalization.monic p d N) (PaddedIntegralNormalization.natDegree p d N)

theorem relativeBasis_apply (p :A[X]) (d N :ℕ) (i :Fin N) :
    relativeBasis p d N i=AdjoinRoot.root (PaddedIntegralNormalization.polynomial p d N)^i.val:=
  IntegralCoordinateBasis.relativeBasis_apply _ _ _ _

theorem relativeBasis_repr_mk (p q :A[X]) (d N :ℕ) (i :Fin N) :
    (relativeBasis p d N).repr (AdjoinRoot.mk _ q) i=
      (q %ₘ PaddedIntegralNormalization.polynomial p d N).coeff i.val:=by
  simp only [relativeBasis,IntegralCoordinateBasis.relativeBasis,Module.Basis.repr_reindex_apply]
  change (AdjoinRoot.modByMonicHom (PaddedIntegralNormalization.monic p d N)
    (AdjoinRoot.mk _ q)).coeff i.val=_
  rw [AdjoinRoot.modByMonicHom_mk]

theorem specialize_relativeBasis (φ :A→+*B) (p :A[X]) (d N :ℕ) (i :Fin N) :
    specialize φ p d N (relativeBasis p d N i)=relativeBasis (p.map φ) d N i:=by
  rw [relativeBasis_apply,map_pow,specialize_root,relativeBasis_apply]

theorem relativeBasis_repr_specialize (φ :A→+*B) (p :A[X]) (d N :ℕ)
    (a :Extension p d N) (i :Fin N) :
    (relativeBasis (p.map φ) d N).repr (specialize φ p d N a) i=
      φ ((relativeBasis p d N).repr a i):=by
  induction a using AdjoinRoot.induction_on with
  | ih q=>
    rw [specialize_mk,relativeBasis_repr_mk,relativeBasis_repr_mk]
    rw [←Polynomial.coeff_map,Polynomial.map_modByMonic φ (PaddedIntegralNormalization.monic p d N),
      PaddedIntegralNormalization.map]

end Basis

section Algebras
variable {R :Type*} [CommRing R] [Algebra R A] [Algebra R B]

noncomputable def specializeAlgHom (φ :A→ₐ[R]B) (p :A[X]) (d N :ℕ) :
    Extension p d N→ₐ[R]Extension (p.map φ.toRingHom) d N where
  __:=specialize φ.toRingHom p d N
  commutes' r:=by
    change specialize φ.toRingHom p d N (AdjoinRoot.of _ (algebraMap R A r))=
      AdjoinRoot.of _ (algebraMap R B r)
    rw [specialize_of]
    exact congrArg (AdjoinRoot.of _) (φ.commutes r)

theorem specializeAlgHom_apply (φ :A→ₐ[R]B) (p :A[X]) (d N :ℕ) (a :Extension p d N) :
    specializeAlgHom φ p d N a=specialize φ.toRingHom p d N a:=rfl

end Algebras
end PaddedIntegralParameterExtension
end LeanCanny.Algebra
