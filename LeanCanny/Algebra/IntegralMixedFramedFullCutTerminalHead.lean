/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutHeadReader
public import LeanCanny.Algebra.FixedWidthBivariateSuffixSpace
/-! # Full relative factors on the terminal scalar suffix with one unused axis

The first variable is unused. All creating raw variables occupy their
literal suffix in the terminal bank; a count guard rejects invalid layouts.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedFullCutHead (arity head headDegree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d : List Bool→ℕ)

noncomputable def count (c : List Bool) :=(atKey P D H (terminal c)).count
noncomputable def newer (c : List Bool) :=count P D H terminal c-arity P D H parent c+1
abbrev Valid (c : List Bool) :=arity P D H parent c≤count P D H terminal c

theorem count_unary (a : Access P) (ht : terminal∈FP) : UnaryFn (count P D H terminal) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht

theorem newer_unary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP) : UnaryFn (newer P D H parent terminal) :=
  (((count_unary P D H terminal a ht).sub (IntegralMixedFramedFullCutHead.arity_unary P D H parent a hp)).add (UnaryFn.const 1))

theorem valid_FP (a : Access P) (hp : parent∈FP) (ht : terminal∈FP) : FPPred (Valid P D H parent terminal) :=
  (BinaryFn.ofUnary (IntegralMixedFramedFullCutHead.arity_unary P D H parent a hp)).le
    (BinaryFn.ofUnary (count_unary P D H terminal a ht))

theorem arity_eq (c : List Bool) (hc : Valid P D H parent terminal c) :
    newer P D H parent terminal c+arity P D H parent c=count P D H terminal c+1 :=by
  unfold newer
  omega

noncomputable def castHead {m n : ℕ} (h : m=n) (p : Polynomial (MvPolynomial (Fin m) ℤ)) :
    Polynomial (MvPolynomial (Fin n) ℤ) :=p.map (MvPolynomial.rename (Fin.cast h)).toRingHom

private theorem castHead_heq {m n : ℕ} (h : m=n) (p : Polynomial (MvPolynomial (Fin m) ℤ)) : HEq (castHead h p) p :=by
  cases h
  simp [castHead]

noncomputable def polynomial (c : List Bool) : Polynomial (MvPolynomial (Fin (count P D H terminal c+1)) ℤ) :=
  if hc : Valid P D H parent terminal c then
    castHead (arity_eq P D H parent terminal c hc)
      (FixedWidthBivariateSuffixBits.polynomial (newer P D H parent terminal) (arity P D H parent)
        (head P D H parent d) c) else 0

theorem polynomial_heq (c : List Bool) (hc : Valid P D H parent terminal c) :
    HEq (polynomial P D H parent terminal d c)
      (FixedWidthBivariateSuffixBits.polynomial (newer P D H parent terminal) (arity P D H parent)
        (head P D H parent d) c) :=by
  rw [polynomial,dite_eq_left hc]
  exact castHead_heq _ _

private theorem value_congr {m n : ℕ} (p : Polynomial (MvPolynomial (Fin m) ℤ))
    (q : Polynomial (MvPolynomial (Fin n) ℤ)) (h : m=n) (hp : HEq p q) (W y : ℕ) (r mw : List Bool) :
    residueBits ((((p.coeff y).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r))) : ℤ) :
      ZMod (Nat.fromBitsLE mw+1))=
    residueBits ((((q.coeff y).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W (Nat.fromBitsLE r))) : ℤ) :
      ZMod (Nat.fromBitsLE mw+1)) :=by
  cases h
  cases hp
  rfl

theorem coefficient_evaluator (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (hp : parent∈FP) (ht : terminal∈FP) (W y : List Bool→ℕ) (hd : BinaryFn d) (hW : UnaryFn W) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (hT : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>count P D H terminal c+1) W
      (fun c=>(polynomial P D H parent terminal d c).coeff (y c)) target modulus) :=by
  have HN:=newer_unary P D H parent terminal a hp ht
  have EO:=IntegralMixedFramedFullCutHead.coefficient_evaluator P D H a L F C hL hF hC h hb parent hp d y W hd hy hW
    (FixedWidthSuffixLiftBits.spatial (newer P D H parent terminal) W target) modulus
    (FixedWidthSuffixLiftBits.spatial_FP _ _ _ HN hW hT) hM
  have E:=FixedWidthSuffixLiftBits.evaluator (newer P D H parent terminal) (arity P D H parent) W
    (fun c=>(head P D H parent d c).coeff (y c)) target modulus HN hW hT EO
  have EB:=SpaceFunction.branch (fun c=>decide (Valid P D H parent terminal c))
    (valid_FP P D H parent terminal a hp ht).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c=>?_)
  by_cases hc : Valid P D H parent terminal c
  · simp only [hc,decide_true,ite_true]
    have HP:=polynomial_heq P D H parent terminal d c hc
    have HV:=value_congr _ _ (arity_eq P D H parent terminal c hc) HP.symm (W c) (y c) (target c) (modulus c)
    simpa only [FixedWidthRowBits.value,FixedWidthBivariateSuffixBits.coefficient] using HV
  · simp only [hc,decide_false,Bool.false_eq_true,ite_false]
    have HZ : polynomial P D H parent terminal d c=0 :=dite_eq_right hc
    change []=residueBits (((((polynomial P D H parent terminal d c).coeff (y c)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c)))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c)+1))
    rw [HZ,Polynomial.coeff_zero,AddMonoidAlgebra.coeff_zero]
    rfl

theorem coefficient_degree (c : List Bool) (y : ℕ) :
    ((polynomial P D H parent terminal d c).coeff y).totalDegree≤headDegree P D H parent c :=by
  unfold polynomial
  split_ifs
  · rw [castHead,Polynomial.coeff_map]
    exact (MvPolynomial.totalDegree_rename_le _ _).trans
      ((FixedWidthBivariateSuffixBits.coefficient_degree _ _ _ c y).trans
        (IntegralMixedFramedFullCutHead.head_coefficient_degree P D H parent d c y))
  · simp

theorem outer_degree (c : List Bool) :
    (polynomial P D H parent terminal d c).natDegree≤IntegralMixedFramedFullCutHead.degree P parent d c :=by
  unfold polynomial
  split_ifs
  · exact Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans
      (IntegralMixedFramedFullCutHead.head_degree P D H parent d c))
  · simp

end LeanCanny.Algebra.IntegralMixedFramedFullCutTerminalHead
