/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateParameterSuffix
/-! # Creating coordinate heads on the exact terminal raw-variable type

A native prefix-count guard rejects inconsistent requests. For valid
counts, only an equality cast changes the enlarged suffix layout to the
literal terminal count; the independent parameter remains first.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHeadBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateCoefficientSpaceBits (arity)
open IntegralMixedFramedCoordinatePackedBits (degreeBound)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedCoordinateParameterSuffixBits (newer)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def castHead {m n : ℕ} (h : m=n) (p : Polynomial (MvPolynomial (Fin m) ℤ)) :
    Polynomial (MvPolynomial (Fin n) ℤ) :=p.map (MvPolynomial.rename (Fin.cast h)).toRingHom

theorem castHead_heq {m n : ℕ} (h : m=n) (p : Polynomial (MvPolynomial (Fin m) ℤ)) : HEq (castHead h p) p :=by
  cases h
  simp [castHead]

private theorem value_congr {m n : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℤ))
    (q : Polynomial (MvPolynomial (Fin n) ℤ)) (h : m=n) (hp : HEq p q) (W y : ℕ) (r mw : List Bool) :
    residueBits ((((p.coeff y).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r))) : ℤ) :
      ZMod (Nat.fromBitsLE mw+1))=
    residueBits ((((q.coeff y).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r))) : ℤ) :
      ZMod (Nat.fromBitsLE mw+1)) :=by
  cases h
  cases hp
  rfl

abbrev Valid (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (c : List Bool) : Prop :=
  arity P D H parent c≤(atKey P D H (terminal c)).count

theorem valid_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP) : FPPred (Valid P D H parent terminal) :=
  (BinaryFn.ofUnary (IntegralMixedFramedCoordinateParameterSuffixBits.arity_unary P a D H parent hp)).le
    (BinaryFn.ofUnary ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht))

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) :
    Polynomial (MvPolynomial (Fin ((atKey P D H (terminal c)).count+1)) ℤ) :=
  if hc : Valid P D H parent terminal c then
    castHead (IntegralMixedFramedCoordinateParameterSuffixBits.arity_eq_terminal P D H parent terminal c hc)
      (IntegralMixedFramedCoordinateParameterSuffixBits.polynomial P D H parent terminal d e c) else 0

theorem polynomial_heq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) (hc : Valid P D H parent terminal c) :
    HEq (polynomial P D H parent terminal d e c)
      (IntegralMixedFramedCoordinateParameterSuffixBits.polynomial P D H parent terminal d e c) :=by
  rw [polynomial,dite_eq_left hc]
  exact castHead_heq _ _

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP)
    (d e y : List Bool→ℕ) (hd : BinaryFn d) (he : BinaryFn e) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (hT : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>(atKey P D H (terminal c)).count+1)
      (nativeWidth P D H parent e) (fun c=>(polynomial P D H parent terminal d e c).coeff (y c)) target modulus) :=by
  have E:=IntegralMixedFramedCoordinateParameterSuffixBits.coefficient_evaluator P a D H L F C hL hF hC I h hb
    parent terminal hp ht d e y hd he hy target modulus hT hM
  have HG:=valid_FP P a D H parent terminal hp ht
  have EB:=SpaceFunction.branch (fun c=>decide (Valid P D H parent terminal c)) HG.flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c=>?_)
  by_cases hc : Valid P D H parent terminal c
  · simp only [hc,decide_true,ite_true]
    exact value_congr _ _ (IntegralMixedFramedCoordinateParameterSuffixBits.arity_eq_terminal P D H parent terminal c hc)
      (HEq.symm (polynomial_heq P D H parent terminal d e c hc)) _ _ _ _
  · simp only [hc,decide_false,Bool.false_eq_true,ite_false]
    have HZ : polynomial P D H parent terminal d e c=0 :=by
      unfold polynomial
      exact dite_eq_right hc
    change []=residueBits (((((polynomial P D H parent terminal d e c).coeff (y c)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (nativeWidth P D H parent e c)
        (Nat.fromBitsLE (target c)))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1))
    rw [HZ,Polynomial.coeff_zero,AddMonoidAlgebra.coeff_zero]
    simp only [Finsupp.zero_apply,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem coefficient_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) (y : ℕ) :
    ((polynomial P D H parent terminal d e c).coeff y).totalDegree≤degreeBound P D H parent e c :=by
  unfold polynomial
  split_ifs
  · rw [castHead,Polynomial.coeff_map]
    exact (MvPolynomial.totalDegree_rename_le _ _).trans
      (IntegralMixedFramedCoordinateParameterSuffixBits.coefficient_degree P D H parent terminal d e c y)
  · simp

end LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHeadBits
