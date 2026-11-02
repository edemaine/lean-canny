/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFramedRowPolynomial
public import LeanCanny.Algebra.PaddedIntegralRowComp

/-! # Native actual prefix rows from their original creating companions

The requested row selects one original creator. Its native monic-row reader
works in the original variable block; an FP support guard rejects younger
variables and repacks the surviving exponent query. Every arithmetic cost
is charged to the actual companion source evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionBits FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedCompanionBits.source PaddedIntegralRowBits.polynomial

noncomputable def reader (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (V : List Bool→ℕ) (modulus : List Bool→List Bool) (p : List Bool) : List Bool :=
  residueBits (((PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1)
      (creatorKey P key index (pairFst p))).coeff
    (nativeExponent (Equiv.refl (Fin ((source P D H).arity (creatorKey P key index (pairFst p))+1)))
      (V (pairFst p)) (Nat.fromBitsLE (pairSnd p))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst p))+1))

theorem reader_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key index : List Bool→List Bool)
    (V : List Bool→ℕ) (modulus : List Bool→List Bool)
    (hk : key∈FP) (hi : index∈FP) (hV : UnaryFn V) (hm : modulus∈FP)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value (source P D H))) :
    SpaceFunction (reader P D H key index V modulus) := by
  have HF := mem_FP_comp pairFst_mem_FP (creatorKey_FP P a key index hk hi)
  have HC : UnaryFn (fun key=>P.cap (pairFst key)+1) := (a.cap.comp pairFst_mem_FP).add (UnaryFn.const 1)
  have Hrow := PaddedIntegralRowBits.comp_row_evaluator (source P D H) (creatorKey P key index ∘ pairFst)
    (fun key=>P.cap (pairFst key)+1) (V ∘ pairFst) pairSnd (modulus ∘ pairFst) HF HC
    (source_arity_unary P a D H) (source_width_unary P a D H) (hV.comp pairFst_mem_FP)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm) E
  exact Hrow.congr (funext fun _=>rfl)

theorem reader_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key index : List Bool→List Bool) (V : List Bool→ℕ) (modulus : List Bool→List Bool)
    (q : List Bool) (r : ℕ) :
    reader P D H key index V modulus (pair q (BinaryNatCode.encode r)) =
      residueBits (((PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1)
        (creatorKey P key index q)).coeff
        (nativeExponent (Equiv.refl (Fin ((source P D H).arity (creatorKey P key index q)+1))) (V q) r) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  generalize HZ : pair q (BinaryNatCode.encode r)=p
  have HQ : pairFst p=q := by rw [←HZ,pairFst_pair]
  have HR : Nat.fromBitsLE (pairSnd p)=r := by rw [←HZ,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  subst q
  simp only [reader,HR]

theorem polynomial_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key index target modulus : List Bool→List Bool)
    (hpos : ∀ q,0<count P key q) (V : List Bool→ℕ)
    (hk : key∈FP) (hi : index∈FP) (hV : UnaryFn V) (ht : target∈FP) (hm : modulus∈FP)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value (source P D H))) :
    SpaceFunction (FixedWidthRowBits.value (count P key) V (polynomial P D H key index hpos) target modulus) := by
  let A := fun q=>(source P D H).arity (creatorKey P key index q)+1
  have HA : UnaryFn A := ((source_arity_unary P a D H).comp (creatorKey_FP P a key index hk hi)).add (UnaryFn.const 1)
  have Hreader := reader_evaluator P a D H key index V modulus hk hi hV hm E
  have HBlock := FixedWidthBlockRenameBits.evaluator A (count P key) (selected P key index) V target Hreader
    HA (count_unary P a key hk) (selected_unary P a key index hk hi) hV ht
  apply HBlock.congr
  funext q
  exact FixedWidthBlockRenameBits.packet A (count P key) (selected P key index) V target
    (PaddedIntegralRowBits.polynomial (source P D H) (fun key=>P.cap (pairFst key)+1) (creatorKey P key index q))
    (row_fit P D H key index hpos q) (reader P D H key index V modulus) q (Nat.fromBitsLE (modulus q)+1)
    rfl rfl rfl (reader_packet P D H key index V modulus q)

end LeanCanny.Algebra.IntegralMixedFramedRowBits
