/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar
public import LeanCanny.Algebra.IntegralHistoryRealExtension
/-! # A reserved scalar probe has a correlated zero-padding realization

Only d<N is required. Zero need not be a root of the unpadded factor. This
extension is for virtual interval probes, not meaningful endpoint records.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open IntegralHistorySampler UniformIntegralPrefix UniformIntegralPowerSchedule Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem normalizedScalar_padding_zero_extend (x : State P S B m ι) (hm : m≤S)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (d : ℕ) (hd : d<2^B)
    (z : ι→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i) :
    ∃y : (ι⊕Unit)→ℝ,∃ψ : (normalizedScalarStep x hm p d).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,((normalizedScalarStep x hm p d).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀i,y (Sum.inl i)=z i) ∧ y (Sum.inr ())=0 ∧
      ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ ∧
      (∀i,ψ ((normalizedScalarStep x hm p d).sampler.scalarPrefix.basis.generator i)=
        y ((normalizedScalarStep x hm p d).sampler.scalar i)^weights S (2^B) (m+1) i) ∧
      ψ ((normalizedScalarStep x hm p d).bank.numerator 0)/
        ((normalizedScalarStep x hm p d).bank.denominator 0:ℝ)=0 ∧
      ∀i,ψ ((normalizedScalarStep x hm p d).bank.numerator i.succ)/
        ((normalizedScalarStep x hm p d).bank.denominator i.succ:ℝ)=
          φ (x.bank.numerator i)/(x.bank.denominator i:ℝ):=by
 let q:=normalizedScalarPolynomial x p d
 have H0 : (PaddedIntegralParameterExtension.equation x.sampler.scalarPrefix.basis q d).eval₂
     (MvPolynomial.aeval (fun i=>φ (x.sampler.scalarPrefix.basis.generator i))).toRingHom (0:ℝ)=0:=by
   rw [PaddedIntegralParameterExtension.equation,x.sampler.scalarPrefix.basis.polynomial_eval]
   simp only [PaddedIntegralNormalization.polynomial,ite_eq_left hd.le,eval₂_mul,eval₂_pow,eval₂_X,
     zero_pow (Nat.sub_pos_of_lt hd).ne',zero_mul]
 obtain ⟨y,hy,htail,hhead⟩:=scalarStep_real_extend x.sampler hm (Nat.two_pow_pos B) q d z hz φ hφ 0 H0
 have Hscalar : y (Sum.inr ())=0:=(pow_eq_zero_iff (birth_pos S (2^B) m).ne').mp hhead
 obtain ⟨ψ,hψ⟩:=(scalarStep x.sampler hm (Nat.two_pow_pos B) q d).interpret ℝ y hy
 have HR : ψ.comp (AdjoinRoot.ofAlgHom ℤ _)=φ:=by
   apply x.sampler.scalarPrefix.basis.algHom_ext
   intro i
   have HI:=hψ i.succ
   change ψ (AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator i))=
     y (Sum.inl (x.sampler.scalar i))^weights S (2^B) (m+1) i.succ at HI
   rw [old,htail] at HI
   exact HI.trans (hφ i).symm
 refine ⟨y,ψ,hy,htail,Hscalar,HR,hψ,?_,?_⟩
 · change ψ (AdjoinRoot.root _)/(normalizedScalarLeading x p d:ℝ)=0
   have HI:=hψ (0:Fin (m+1))
   change ψ (AdjoinRoot.root _)=y (Sum.inr ())^weights S (2^B) (m+1) 0 at HI
   rw [HI,Hscalar,zero_pow (weights_pos S (2^B) (m+1) 0).ne',zero_div]
 · intro i
   have HE:=congrArg (fun χ=>χ (x.bank.numerator i)) HR
   change ψ (AdjoinRoot.of _ (x.bank.numerator i))/(x.bank.denominator i:ℝ)=_
   exact congrArg (fun a : ℝ=>a/(x.bank.denominator i:ℝ)) HE

end LeanCanny.Algebra.IntegralMixedHistory
