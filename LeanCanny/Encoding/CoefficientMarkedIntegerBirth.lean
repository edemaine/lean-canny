/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusDegree
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
public import LeanCanny.Algebra.CoefficientHeightBankScalarStep
/-! # Actual marked integer births from one formal radius polynomial

Every native leaf tag, including slack/default leaves, has its actual fixed
degree and leading scalar. No degree-preservation premise is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedIntegerBirth
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→LeanCanny.ETR.Term}
  (hn :UnaryFn n) (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)

noncomputable def leaf (ctx :List Bool) (i :ℕ) :(ℤ[X])[X]:=
  IntegralMixedAuxiliaryMarkedRadiusModel.polynomial hn ht ha (pair ctx (BinaryNatCode.encode i))

noncomputable def width (ctx:List Bool):ℕ:=
  (IntegralMixedAuxiliaryMarkedIntegerPlan.parameters hn ht ha).width ctx

section Birth
variable {A :Type*} [CommRing A] [Algebra ℤ[X] A]
  {ambient cap m :ℕ} {P :SpatialSource ambient} {ι :Type} [Fintype ι]
  (ctx :List Bool) (i :ℕ) (radius :List Bool→ℕ)
variable (bank :CoefficientHeightBank ℤ[X] A m) (b :CoefficientCoordinateBasis ℤ[X] A m (2^(width hn ht ha ctx)))
  (x :State P cap (width hn ht ha ctx) m ι) (hm :m≤cap)
  (ψ :A→+*x.sampler.scalarPrefix.carrier)
  (HB :CoefficientHeightBank.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx)) ψ bank
    (CoefficientHeightBank.ofState x))
  (Hb :CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx)) ψ b
    (CoefficientCoordinateBasis.ofIntegral x.sampler.scalarPrefix.basis))

noncomputable def polynomial :A[X]:=(leaf hn ht ha ctx i).map (algebraMap ℤ[X] A)

noncomputable def nativeStep :=
  integerStep x hm ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
    (pair ctx (BinaryNatCode.encode i)))
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha radius _)
    (((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).degree_bound _).trans
      (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha radius ctx i))

include HB

omit [Fintype ι] in
theorem polynomial_map_native :
    (polynomial hn ht ha ctx i (A:=A)).map ψ=
      ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
        (pair ctx (BinaryNatCode.encode i))).map (Int.castRingHom x.sampler.scalarPrefix.carrier):=by
  have HC :ψ.comp (algebraMap ℤ[X] A)=
      (Int.castRingHom x.sampler.scalarPrefix.carrier).comp (Polynomial.evalRingHom ((2:ℤ)^radius ctx)):=by
    apply RingHom.ext
    intro z
    exact HB.coefficients z
  rw [polynomial,Polynomial.map_map,HC,←Polynomial.map_map]
  have HP:=IntegralMixedAuxiliaryMarkedRadiusModel.polynomial_map_eval hn ht ha radius
    (pair ctx (BinaryNatCode.encode i))
  simpa only [leaf,pairFst_pair] using congrArg
    (fun p=>p.map (Int.castRingHom x.sampler.scalarPrefix.carrier)) HP

noncomputable def specialize :
    PaddedIntegralParameterExtension.Extension (polynomial hn ht ha ctx i (A:=A))
      (leaf hn ht ha ctx i).natDegree (2^(width hn ht ha ctx))→+*(nativeStep hn ht ha ctx i radius x hm).sampler.scalarPrefix.carrier:=by
  change PaddedIntegralParameterExtension.Extension _ _ _→+*
    PaddedIntegralParameterExtension.Extension _ _ _
  exact AdjoinRoot.map ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native hn ht ha ctx i radius bank x ψ HB,
      IntegralMixedAuxiliaryMarkedRadiusModel.native_natDegree]
    rfl)

theorem specialize_of (v :A):
    specialize hn ht ha ctx i radius bank x hm ψ HB (AdjoinRoot.of _ v)=AdjoinRoot.of _ (ψ v):=by
  exact AdjoinRoot.map_of ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native hn ht ha ctx i radius bank x ψ HB,
      IntegralMixedAuxiliaryMarkedRadiusModel.native_natDegree]
    rfl) v

theorem specialize_root :
    specialize hn ht ha ctx i radius bank x hm ψ HB (AdjoinRoot.root _)=AdjoinRoot.root _:=by
  exact AdjoinRoot.map_root ψ _ _ (by
    rw [PaddedIntegralNormalization.map,polynomial_map_native hn ht ha ctx i radius bank x ψ HB,
      IntegralMixedAuxiliaryMarkedRadiusModel.native_natDegree]
    rfl)

include Hb

theorem basis_specializes [Nontrivial A] :
    CoefficientCoordinateBasis.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx))
      (specialize hn ht ha ctx i radius bank x hm ψ HB)
      (b.paddedStep (polynomial hn ht ha ctx i (A:=A)) (leaf hn ht ha ctx i).natDegree)
      (CoefficientCoordinateBasis.ofIntegral (nativeStep hn ht ha ctx i radius x hm).sampler.scalarPrefix.basis):=by
  constructor
  · intro z
    change specialize hn ht ha ctx i radius bank x hm ψ HB
      (AdjoinRoot.of _ (algebraMap ℤ[X] A z))=AdjoinRoot.of _
        (algebraMap ℤ x.sampler.scalarPrefix.carrier ((Polynomial.evalRingHom ((2:ℤ)^radius ctx)) z))
    rw [specialize_of,Hb.coefficients]
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · exact specialize_root hn ht ha ctx i radius bank x hm ψ HB
    · change specialize hn ht ha ctx i radius bank x hm ψ HB
        (AdjoinRoot.of _ (b.generator k))=AdjoinRoot.of _ (x.sampler.scalarPrefix.basis.generator k)
      rw [specialize_of,Hb.generators]
      rfl

omit Hb in
theorem bank_specializes :
    CoefficientHeightBank.Specializes (Polynomial.evalRingHom ((2:ℤ)^radius ctx))
      (specialize hn ht ha ctx i radius bank x hm ψ HB)
      (bank.rootStep (polynomial hn ht ha ctx i (A:=A)) (leaf hn ht ha ctx i).natDegree
        (2^(width hn ht ha ctx)) (leaf hn ht ha ctx i).leadingCoeff)
      (CoefficientHeightBank.ofState (nativeStep hn ht ha ctx i radius x hm)):=by
  constructor
  · intro z
    change specialize hn ht ha ctx i radius bank x hm ψ HB
      (AdjoinRoot.of _ (algebraMap ℤ[X] A z))=AdjoinRoot.of _
        (algebraMap ℤ x.sampler.scalarPrefix.carrier ((Polynomial.evalRingHom ((2:ℤ)^radius ctx)) z))
    rw [specialize_of,HB.coefficients]
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · exact specialize_root hn ht ha ctx i radius bank x hm ψ HB
    · change specialize hn ht ha ctx i radius bank x hm ψ HB
        (AdjoinRoot.of _ (bank.numerator k))=AdjoinRoot.of _ (x.bank.numerator k)
      rw [specialize_of,HB.numerator]
      rfl
  · intro j
    refine Fin.cases ?_ (fun k=>?_) j
    · change (leaf hn ht ha ctx i).leadingCoeff.eval ((2:ℤ)^radius ctx)=
        ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
          (pair ctx (BinaryNatCode.encode i))).leadingCoeff
      simpa only [leaf,pairFst_pair] using (IntegralMixedAuxiliaryMarkedRadiusModel.native_leadingCoeff hn ht ha radius
        (pair ctx (BinaryNatCode.encode i))).symm
    · exact HB.denominator k

theorem rows_map_native (q :ι→MvPolynomial ι ℤ[X])
    (HQ :∀j,MvPolynomial.map (Polynomial.evalRingHom ((2:ℤ)^radius ctx)) (q j)=x.sampler.rows j):
    (fun j=>MvPolynomial.map (Polynomial.evalRingHom ((2:ℤ)^radius ctx))
      (CoefficientCanonicalScalarAppend.rows cap q x.sampler.scalar b
        (polynomial hn ht ha ctx i (A:=A)) (leaf hn ht ha ctx i).natDegree j))=
      (nativeStep hn ht ha ctx i radius x hm).sampler.rows:=by
  rw [CoefficientCanonicalScalarAppend.newrows_map Hb cap q x.sampler.rows HQ]
  rw [polynomial_map_native hn ht ha ctx i radius bank x ψ HB]
  change CanonicalIntegralScalarAppend.rows cap x.sampler.rows x.sampler.scalar x.sampler.scalarPrefix.basis
    (((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
      (pair ctx (BinaryNatCode.encode i))).map (Int.castRingHom x.sampler.scalarPrefix.carrier))
    (leaf hn ht ha ctx i).natDegree=_
  unfold nativeStep integerStep
  rw [IntegralMixedAuxiliaryMarkedRadiusModel.native_natDegree]
  rfl

end Birth
end LeanCanny.Encoding.CoefficientMarkedIntegerBirth
