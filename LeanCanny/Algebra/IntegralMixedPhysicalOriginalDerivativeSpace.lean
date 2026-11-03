/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves
public import LeanCanny.Algebra.FixedWidthBinaryDerivativeSpace
public import LeanCanny.Algebra.FixedWidthPowerMonomial
/-! # Actual original physical derivatives from charged original coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOriginalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

 theorem scalar_native (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (q : List Bool) (r : ℕ) :
    scalar F I (pair q (BinaryNatCode.encode r))=
      residueBits (((F.spatial q).low.coeff (nativeExponent (Equiv.refl (Fin (F.ambient q+1)))
        (F.spatial q).degree.size r)) : ZMod (I.modulus q)) := by
  rw [scalar_packet,IntegralMixedOriginalSpatialTermBits.physical_coefficient,nativeExponent_refl]

noncomputable def derivative (F : IntegralMixedPhysicalCriticalBits.Family) (selected : List Bool→ℕ)
    (hs : ∀q,selected q<F.ambient q+1) (q : List Bool) : MvPolynomial (Fin (F.ambient q+1)) ℤ :=
  MvPolynomial.pderiv ⟨selected q,hs q⟩ (F.spatial q).low

theorem derivative_evaluator (F : IntegralMixedPhysicalCriticalBits.Family)
    (I : IntegralMixedPhysicalCriticalBits.Indices F) (h : IntegralMixedPhysicalCriticalBits.Metadata F I)
    (original : SpaceFunction (scalar F I)) (selected : List Bool→ℕ) (hs : ∀q,selected q<F.ambient q+1)
    (hselected : UnaryFn selected) (V : List Bool→ℕ) (hV : UnaryFn V)
    (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V (derivative F selected hs) target
      (fun q=>BinaryNatCode.encode (I.modulus q-1))) := by
  let A:=fun q=>F.ambient q+1
  let W:=fun q=>(F.spatial q).degree.size
  let D:=fun q=>(F.spatial q).degree
  have hA : UnaryFn A:=h.ambient.add (UnaryFn.const 1)
  have hW : UnaryFn W:=IntegralMixedPhysicalCriticalBits.sourceWidth_unary F I h
  have HE:=FixedWidthDerivativeBits.evaluator_binary A W V D selected target
    (fun q=>BinaryNatCode.encode (I.modulus q)) original hA hW hV h.degree hselected ht h.modulus.bits_mem_FP
  apply HE.congr
  funext q
  have HP:=FixedWidthDerivativeBits.packet A W V D selected target (fun q=>BinaryNatCode.encode (I.modulus q))
    (Equiv.refl (Fin (F.ambient q+1))) (scalar F I) q (F.spatial q).low ⟨selected q,hs q⟩ (I.modulus q)
    rfl rfl (by change 0<(F.spatial q).degree; have H:=(F.spatial q).degree_two;omega) (F.spatial q).low_degree.le
    (Nat.lt_size_self _) rfl (fun r=>scalar_native F I q r)
  have HX : FixedWidthDerivativeBits.exponent V target (Equiv.refl (Fin (F.ambient q+1))) q=
      nativeExponent (Equiv.refl (Fin (F.ambient q+1))) (V q) (Nat.fromBitsLE (target q)) := by
    ext i
    simp only [FixedWidthDerivativeBits.exponent,Finsupp.coe_equivFunOnFinite_symm,Equiv.refl_apply]
    exact (FixedWidthPowerMonomial.native_coordinate A V target q i).symm
  have HM : I.modulus q=Nat.fromBitsLE (BinaryNatCode.encode (I.modulus q-1))+1 := by
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H:=I.modulus_ne_zero q
    omega
  exact HP.trans (congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m))
    (congrArg (MvPolynomial.pderiv (⟨selected q,hs q⟩ : Fin (F.ambient q+1)) (F.spatial q).low).coeff HX) HM)

end LeanCanny.Algebra.IntegralMixedPhysicalOriginalBits
