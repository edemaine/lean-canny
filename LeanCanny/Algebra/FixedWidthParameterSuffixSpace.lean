/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthSuffixLiftSpace
public import LeanCanny.Algebra.FixedWidthPermutationSpace
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Suffix embedding preserves an independent parameter at the first slot

New terminal raw variables are unused. A transposition puts the parameter
back at zero; all old raw variables retain their literal terminal suffix.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthParameterSuffixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

def pivot (d a : ℕ) : Fin (d+(a+1)) :=⟨d,by omega⟩
noncomputable def headSwap (d a : ℕ) : Equiv.Perm (Fin (d+(a+1))) :=Equiv.swap 0 (pivot d a)
noncomputable def shift (d : ℕ) {a : ℕ} (i : Fin (a+1)) : Fin (d+(a+1)) :=
  headSwap d a (FixedWidthSuffixLiftBits.shift d i)

theorem shift_injective (d a : ℕ) : Function.Injective (shift d : Fin (a+1)→Fin (d+(a+1))) :=
  (headSwap d a).injective.comp (FixedWidthSuffixLiftBits.shift_injective d (a+1))

theorem shift_zero (d a : ℕ) : shift d (0 : Fin (a+1))=0 :=by
  change Equiv.swap 0 (pivot d a) (pivot d a)=0
  exact Equiv.swap_apply_right _ _

theorem shift_succ (d a : ℕ) (i : Fin a) :
    shift d i.succ=⟨d+(i.val+1),by omega⟩ :=by
  have H0 : FixedWidthSuffixLiftBits.shift d i.succ≠0 :=by
    intro h
    have HH:=congrArg Fin.val h
    simp only [FixedWidthSuffixLiftBits.shift,Fin.val_zero,Fin.val_succ] at HH
    omega
  have HD : FixedWidthSuffixLiftBits.shift d i.succ≠pivot d a :=by
    intro h
    have HH:=congrArg Fin.val h
    simp only [FixedWidthSuffixLiftBits.shift,pivot,Fin.val_succ] at HH
    omega
  exact Equiv.swap_apply_of_ne_of_ne H0 HD

def inverseIndex (D : List Bool→ℕ) (q : List Bool) : ℕ :=
  if Nat.fromBitsLE (pairSnd q)=0 then D (pairFst q)
    else if Nat.fromBitsLE (pairSnd q)=D (pairFst q) then 0 else Nat.fromBitsLE (pairSnd q)
def inverse (D : List Bool→ℕ) (q : List Bool) :=BinaryNatCode.encode (inverseIndex D q)

theorem inverse_FP (D : List Bool→ℕ) (hD : UnaryFn D) : inverse D∈FP :=by
  have HI:=BinaryFn.fromBits pairSnd_mem_FP
  have HD:=BinaryFn.ofUnary hD.lift
  exact (BinaryFn.ite (HI.eq (BinaryFn.const 0)) HD
    (BinaryFn.ite (HI.eq HD) (BinaryFn.const 0) HI)).bits_mem_FP

theorem inverse_packet (D A : List Bool→ℕ) (c : List Bool) (i : Fin (D c+(A c+1))) :
    inverse D (pair c (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode ((headSwap (D c) (A c)).symm i).val :=by
  simp only [inverse,inverseIndex,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    headSwap,Equiv.symm_swap,Equiv.swap_apply_def,pivot,Fin.ext_iff,Fin.val_zero]
  split_ifs <;> rfl

noncomputable def polynomial (D A : List Bool→ℕ)
    (p : (c : List Bool)→MvPolynomial (Fin (A c+1)) ℤ) (c : List Bool) :=
  MvPolynomial.rename (shift (D c)) (p c)

def word (D A W : List Bool→ℕ) (target : List Bool→List Bool) :=
  FixedWidthPermutationBits.word (fun c=>D c+(A c+1)) W target (inverse D)

theorem word_FP (D A W : List Bool→ℕ) (target : List Bool→List Bool)
    (hD : UnaryFn D) (hA : UnaryFn A) (hW : UnaryFn W) (ht : target∈FP) : word D A W target∈FP :=
  FixedWidthPermutationBits.word_FP _ W target (inverse D) (hD.add (hA.add (UnaryFn.const 1))) hW ht (inverse_FP D hD)

private theorem exponent (A W : List Bool→ℕ) (target : List Bool→List Bool) (c : List Bool) :
    nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))=
      RationalSubstitution.Indexed.exponentVector (A c) (FixedWidthQuery.coordinate W target c) :=by
  ext i
  exact FixedWidthBlockRenameBits.entry_bits _ _ _

theorem evaluator (D A W : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c+1)) ℤ)
    (target modulus : List Bool→List Bool) (hD : UnaryFn D) (hA : UnaryFn A) (hW : UnaryFn W) (ht : target∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value (fun c=>A c+1) W p
      (FixedWidthSuffixLiftBits.spatial D W (word D A W target)) modulus)) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>D c+(A c+1)) W (polynomial D A p) target modulus) :=by
  have HW:=word_FP D A W target hD hA hW ht
  have ES:=FixedWidthSuffixLiftBits.evaluator D (fun c=>A c+1) W p (word D A W target) modulus hD hW HW E
  refine ES.congr (funext fun c=>?_)
  apply congrArg (fun a : ℤ=>residueBits (a : ZMod (Nat.fromBitsLE (modulus c)+1)))
  change (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (D c)) (p c)).coeff
      (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (word D A W target c)))=
    (polynomial D A p c).coeff (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c)))
  rw [exponent (fun c=>D c+(A c+1)) W (word D A W target) c,
    exponent (fun c=>D c+(A c+1)) W target c]
  have HP : MvPolynomial.rename (headSwap (D c) (A c)).symm
      (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (D c)) (p c))=polynomial D A p c :=by
    simp only [polynomial,headSwap,Equiv.symm_swap,MvPolynomial.rename_rename]
    rfl
  exact (FixedWidthPermutationBits.coefficient (fun c=>D c+(A c+1)) W target (inverse D) c
    (headSwap (D c) (A c)) (inverse_packet D A c)
    (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (D c)) (p c))).trans
      (congrArg (fun r=>r.coeff (RationalSubstitution.Indexed.exponentVector (D c+(A c+1))
        (FixedWidthQuery.coordinate W target c))) HP)

theorem evaluation {d a : ℕ} (p : MvPolynomial (Fin (a+1)) ℤ) (z : Fin (d+(a+1))→ℝ) :
    (MvPolynomial.rename (shift d) p).eval₂ (Int.castRingHom ℝ) z=
      p.eval₂ (Int.castRingHom ℝ) (fun i=>z (shift d i)) :=by
  rw [MvPolynomial.eval₂_rename]
  rfl

theorem degree (D A : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c+1)) ℤ) (c : List Bool) :
    (polynomial D A p c).totalDegree≤(p c).totalDegree :=MvPolynomial.totalDegree_rename_le _ _
theorem mass (D A : List Bool→ℕ) (p : (c : List Bool)→MvPolynomial (Fin (A c+1)) ℤ) (c : List Bool) :
    MvMass.mass (polynomial D A p c)≤MvMass.mass (p c) :=MvMass.rename_le _ _

end LeanCanny.Algebra.FixedWidthParameterSuffixBits
