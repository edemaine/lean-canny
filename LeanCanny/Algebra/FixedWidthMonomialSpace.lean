/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # One charged scalar residue reads a binary-power coordinate monomial

The power remains binary. Invalid coordinate selectors give the literal
zero polynomial, including in empty arity; power zero is allowed.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthMonomialBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower MvPolynomial
open scoped Classical
variable (A W selected power : List Bool→ℕ) (target : List Bool→List Bool)

def Matches (c : List Bool) : Prop :=selected c<A c ∧ ∀ i<A c,
  FixedWidthQuery.coordinate W target c i=if i=selected c then power c else 0

theorem matches_FP (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected)
    (hp : BinaryFn power) (ht : target∈FP) : FPPred (Matches A W selected power target) :=by
  have hi:=BinaryFn.ofUnary UnaryFn.index
  have he:=hi.eq (hs.comp pairFst_mem_FP)
  have hc:=BinaryFn.fromBits (take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht)
    (UnaryFn.index.mul hW.lift)) hW.lift)
  have H:=(he.and (hc.eq (hp.comp pairFst_mem_FP))).or (he.not.and (hc.eq (BinaryFn.const 0)))
  apply ((hs.lt (BinaryFn.ofUnary hA)).and (FPPred.forall_lt hA H)).of_iff
  intro c
  simp only [Matches,Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,FixedWidthQuery.coordinate]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  by_cases heq : i=selected c <;> simp [heq]

theorem matches_iff (c : List Bool) (i : Fin (A c)) (hi : selected c=i.val) :
    Matches A W selected power target c↔
      nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c))=Finsupp.single i (power c) :=by
  have HE (j : Fin (A c)) : nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (target c)) j=
      FixedWidthQuery.coordinate W target c j.val:=FixedWidthBlockRenameBits.entry_bits _ _ _
  constructor
  · rintro ⟨_,H⟩
    ext j
    rw [HE]
    simpa only [hi,Finsupp.single_apply,Fin.ext_iff,eq_comm] using H j.val j.isLt
  · intro H
    refine ⟨by rw [hi];exact i.isLt,?_⟩
    intro j hj
    have HC:=congrArg (fun e : Fin (A c)→₀ℕ=>e ⟨j,hj⟩) H
    simpa only [HE,hi,Finsupp.single_apply,Fin.ext_iff,eq_comm] using HC

noncomputable def polynomial (a : List Bool→ℤ) (c : List Bool) : MvPolynomial (Fin (A c)) ℤ :=
  if hi : selected c<A c then MvPolynomial.monomial (Finsupp.single ⟨selected c,hi⟩ (power c)) (a c) else 0

noncomputable def value (reader : List Bool→List Bool) (c : List Bool) : List Bool :=
  if Matches A W selected power target c then reader c else []

theorem evaluator (reader : List Bool→List Bool) (E : SpaceFunction reader)
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (hp : BinaryFn power) (ht : target∈FP) :
    SpaceFunction (value A W selected power target reader) :=by
  have HE:=SpaceFunction.branch (fun c=>decide (Matches A W selected power target c))
    (matches_FP A W selected power target hA hW hs hp ht).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact HE.congr (funext fun c=>by simp only [value,decide_eq_true_eq])

theorem value_eq (reader : List Bool→List Bool) (a : List Bool→ℤ) (modulus : List Bool→List Bool)
    (ha : ∀ c,reader c=residueBits (a c : ZMod (Nat.fromBitsLE (modulus c)+1))) (c : List Bool) :
    value A W selected power target reader c=FixedWidthRowBits.value A W (polynomial A selected power a) target modulus c :=by
  unfold value FixedWidthRowBits.value polynomial
  by_cases hi : selected c<A c
  · rw [dite_eq_left hi]
    rw [matches_iff A W selected power target c ⟨selected c,hi⟩ rfl,MvPolynomial.coeff_monomial]
    by_cases he : nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))=
        Finsupp.single (⟨selected c,hi⟩ : Fin (A c)) (power c)
    · simp only [he,ite_true,ha]
    · simp only [he,ite_false,Ne.symm he,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
  · have HM : ¬Matches A W selected power target c:=fun h=>hi h.1
    rw [ite_eq_right HM,dite_eq_right hi]
    change []=residueBits (0 : ZMod (Nat.fromBitsLE (modulus c)+1))
    simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

theorem coefficient_evaluator (a : List Bool→ℤ) (modulus : List Bool→List Bool)
    (reader : List Bool→List Bool) (E : SpaceFunction reader)
    (ha : ∀ c,reader c=residueBits (a c : ZMod (Nat.fromBitsLE (modulus c)+1)))
    (hA : UnaryFn A) (hW : UnaryFn W) (hs : BinaryFn selected) (hp : BinaryFn power) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value A W (polynomial A selected power a) target modulus) :=
  (evaluator A W selected power target reader E hA hW hs hp ht).congr
    (funext fun c=>value_eq A W selected power target reader a modulus ha c)

end LeanCanny.Algebra.FixedWidthMonomialBits
