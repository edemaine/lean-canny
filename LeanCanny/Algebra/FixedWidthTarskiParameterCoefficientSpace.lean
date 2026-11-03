/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthTarskiPrincipalSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic
public import LeanCanny.Algebra.MvTwoParameterEncodedCoefficient
/-! # Native principal coefficients after two independent parameter extractions

The source context and caller modulus are retained. Delta/epsilon indices
outside the declared whole-output box return zero, rather than wrap to
another coefficient. Only actual principal coefficient costs are charged.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthTarskiParameterBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open MvTwoParameterEncodedCoefficient (castPolynomial)
open scoped Classical

variable (F : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool) (m V j δ ε : List Bool→ℕ)
variable (dim : ∀ c,F.arity (read c)=m c+2)

noncomputable def polynomial (c : List Bool) : MvPolynomial (Fin (m c)) ℤ :=
  MvTwoParameterCoefficient.slice
    (castPolynomial (dim c) (FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c))) (δ c) (ε c)

def Fits (c : List Bool) : Prop :=δ c<2^F.width (read c) ∧ ε c<2^F.width (read c)

theorem fits_FP (hW : UnaryFn F.width) (hr : read∈FP) (hδ : BinaryFn δ) (hε : BinaryFn ε) :
    FPPred (Fits F read δ ε) :=by
  have HB:=(BinaryFn.const 2).powUnary (hW.comp hr)
  exact (hδ.lt HB).and (hε.lt HB)

def query (target modulus : List Bool→List Bool) (c : List Bool) :=
  FixedWidthTarskiPrincipalBits.packet (read c) (j c)
    (Nat.fromBitsLE (MvTwoParameterEncodedCoefficient.word m V (F.width ∘ read) δ ε target c)) (modulus c)

theorem query_FP (hW : UnaryFn F.width) (hr : read∈FP) (hm : UnaryFn m) (hV : UnaryFn V)
    (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hM : modulus∈FP) : query F read m V j δ ε target modulus∈FP :=by
  have HW:=MvTwoParameterEncodedCoefficient.word_FP m V (F.width ∘ read) δ ε target hm hV (hW.comp hr) hδ hε ht
  have HI:=BinaryFn.fromBits HW
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hr hj.bits_mem_FP) HI.bits_mem_FP) hM

noncomputable def value (A : FixedWidthTarskiPrincipalBits.Access F) (target modulus : List Bool→List Bool) (c : List Bool) :=
  if Fits F read δ ε c then FixedWidthTarskiPrincipalBits.value A (query F read m V j δ ε target modulus c) else []

theorem evaluator (A : FixedWidthTarskiPrincipalBits.Access F) (hW : UnaryFn F.width) (hr : read∈FP)
    (hm : UnaryFn m) (hV : UnaryFn V) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (value F read m V j δ ε A target modulus) :=by
  have E:=(FixedWidthTarskiPrincipalBits.evaluator A).precompose _ (query_FP F read m V j δ ε hW hr hm hV hj hδ hε target modulus ht hM)
  have B:=SpaceFunction.branch (fun c=>decide (Fits F read δ ε c)) (fits_FP F read δ ε hW hr hδ hε).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact B.congr (funext fun c=>by simp only [value,decide_eq_true_eq,Function.comp_apply])

theorem value_eq (A : FixedWidthTarskiPrincipalBits.Access F)
    (hfit : ∀ c,(FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c)).totalDegree<2^F.width (read c))
    (hV : ∀ c,V c≤F.width (read c)) (target modulus : List Bool→List Bool) (c : List Bool) :
    value F read m V j δ ε A target modulus c=
      residueBits (((polynomial F read m j δ ε dim c).coeff
        (nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c)+1)) :=by
  let p:=castPolynomial (dim c) (FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c))
  have HP : p.totalDegree<2^F.width (read c):=(MvTwoParameterEncodedCoefficient.cast_degree _ _).trans_lt (hfit c)
  by_cases hf : Fits F read δ ε c
  · rw [value,ite_eq_left hf,query,FixedWidthTarskiPrincipalBits.packet_encoded]
    unfold FixedWidthTarskiPrincipalBits.encode
    rw [←MvTwoParameterEncodedCoefficient.cast_encoded (dim c)]
    apply congrArg (fun a : ℤ=>residueBits (a : ZMod (Nat.fromBitsLE (modulus c)+1)))
    exact MvTwoParameterEncodedCoefficient.coefficient m V (F.width ∘ read) δ ε target c p HP (hV c) hf.1 hf.2
  · rw [value,ite_eq_right hf]
    have HZ : MvTwoParameterCoefficient.slice p (δ c) (ε c)=0 :=by
      apply MvTwoParameterCoefficient.eq_zero
      by_cases hd : δ c<2^F.width (read c)
      · have he : 2^F.width (read c)≤ε c:=by unfold Fits at hf;omega
        exact Or.inr (HP.trans_le he)
      · exact Or.inl (HP.trans_le (by omega))
    change []=residueBits (((MvTwoParameterCoefficient.slice p (δ c) (ε c)).coeff
      (nativeExponent (Equiv.refl _) (V c) (Nat.fromBitsLE (target c))) : ℤ) :ZMod (Nat.fromBitsLE (modulus c)+1))
    rw [HZ]
    simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem coefficient_evaluator (A : FixedWidthTarskiPrincipalBits.Access F) (hW : UnaryFn F.width) (hr : read∈FP)
    (hm : UnaryFn m) (hV : UnaryFn V) (hj : BinaryFn j) (hδ : BinaryFn δ) (hε : BinaryFn ε)
    (hfit : ∀ c,(FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c)).totalDegree<2^F.width (read c))
    (hwidth : ∀ c,V c≤F.width (read c)) (target modulus : List Bool→List Bool) (ht : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value m V (polynomial F read m j δ ε dim) target modulus) :=
  (evaluator F read m V j δ ε A hW hr hm hV hj hδ hε target modulus ht hM).congr
    (funext fun c=>value_eq F read m V j δ ε dim A hfit hwidth target modulus c)

theorem degree (c : List Bool) : (polynomial F read m j δ ε dim c).totalDegree≤
    (FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c)).totalDegree :=
  (MvTwoParameterCoefficient.degree _ _ _).trans (MvTwoParameterEncodedCoefficient.cast_degree _ _)
theorem mass (c : List Bool) : MvMass.mass (polynomial F read m j δ ε dim c)≤
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial F (read c) (j c)) :=
  (MvTwoParameterCoefficient.mass _ _ _).trans (MvTwoParameterEncodedCoefficient.cast_mass _ _)

end LeanCanny.Algebra.FixedWidthTarskiParameterBits
