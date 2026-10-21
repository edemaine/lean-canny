/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialExponentAtom
public import LeanCanny.ETR.IntegerResidueFP
public import LeanCanny.Encoding.BinaryPowModFP

/-! # FP modular coefficient accumulation at expression leaves -/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding
open LeanCanny.Algebra.MatrixPower

def coefficientSeed (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.one (BinaryNat.succ (modulus c))

def coefficientLeaf (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  if NNF.HasOne 0 (leafTerm p) then
    Codec.IntegerResidue.value (pair (NNF.second (leafTerm p)) (BinaryNat.succ (modulus (pairFst p))))
  else coefficientSeed modulus (pairFst p)

def coefficientAtom (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNat.succ (modulus (pairFst p)))
    (pair (leafAccumulator p) (coefficientLeaf modulus p)))

theorem coefficientSeed_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : coefficientSeed modulus ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp hm BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  refine mem_FP_of_eq (g := coefficientSeed modulus) h ?_
  intro c
  simp only [coefficientSeed, Function.comp_apply]

theorem coefficientLeaf_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : coefficientLeaf modulus ∈ FP := by
  have hpayload := mem_FP_comp leafTerm_mem_FP NNF.second_mem_FP
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  have hconst := mem_FP_comp (mem_FP_pair hpayload hmod) Codec.IntegerResidue.value_mem_FP
  have hone := mem_FP_comp pairFst_mem_FP (coefficientSeed_mem_FP hm)
  have h := ((NNF.hasOne_fppred 0).comp leafTerm_mem_FP).ite_mem_FP hconst hone
  refine mem_FP_of_eq (g := coefficientLeaf modulus) h ?_
  intro p
  simp only [coefficientLeaf, Function.comp_apply]

theorem coefficientAtom_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : coefficientAtom modulus ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair leafAccumulator_mem_FP (coefficientLeaf_mem_FP hm))) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := coefficientAtom modulus) h ?_
  intro p
  simp only [coefficientAtom, Function.comp_apply]

theorem coefficientSeed_correct (modulus : List Bool → List Bool) (c : List Bool) :
    coefficientSeed modulus c = residueBits (1 : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simpa only [coefficientSeed, BinaryNat.succ_eq_bits, BinaryNatCode.encode] using
    ArithmeticBits.one_residueBits (Nat.fromBitsLE (modulus c) + 1)

theorem coefficientLeaf_const (modulus : List Bool → List Bool) (c v : List Bool) (z : ℤ) :
    coefficientLeaf modulus (pair c (pair (Term.const z).toData.toBits v)) =
      residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
  have htag : NNF.HasOne 0 (Term.const z).toData.toBits := by
    rw [NNF.hasOne_toBits]
    exact ⟨Codec.integer z, rfl⟩
  simp only [coefficientLeaf, leafTerm, pairFst_pair, pairSnd_pair, htag, ↓reduceIte]
  simpa only [NNF.second, Term.toData, Encoding.Brackets.remainingChildren_toBits, Encoding.Brackets.firstChild_toBits,
    BinaryNat.succ_eq_bits, BinaryNatCode.encode] using
    Codec.IntegerResidue.value_integer z (Nat.fromBitsLE (modulus c) + 1)

theorem coefficientLeaf_var (modulus : List Bool → List Bool) (c v : List Bool) (j : ℕ) :
    coefficientLeaf modulus (pair c (pair (Term.var j).toData.toBits v)) =
      residueBits (1 : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have htag : ¬ NNF.HasOne 0 (Term.var j).toData.toBits := by
    simp [NNF.hasOne_toBits, NNF.one, Term.toData, Codec.unary]
  simp only [coefficientLeaf, leafTerm, pairFst_pair, pairSnd_pair, htag, ↓reduceIte, coefficientSeed_correct]

theorem mulMod_residueBits (modulus : List Bool → List Bool) (c : List Bool)
    (a b : ZMod (Nat.fromBitsLE (modulus c) + 1)) :
    BinaryNat.mulMod (pair (BinaryNat.succ (modulus c)) (pair (residueBits a) (residueBits b))) = residueBits (a * b) := by
  let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
  simp only [BinaryNat.mulMod_pair, BinaryNat.succ_eq_bits, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

theorem coefficientAtom_const (modulus : List Bool → List Bool) (c : List Bool) (z : ℤ)
    (v : ZMod (Nat.fromBitsLE (modulus c) + 1)) :
    coefficientAtom modulus (pair c (pair (Term.const z).toData.toBits (residueBits v))) = residueBits (v * (z : ZMod _)) := by
  simp only [coefficientAtom, pairFst_pair, coefficientLeaf_const, leafAccumulator, pairSnd_pair, mulMod_residueBits]

theorem coefficientAtom_var (modulus : List Bool → List Bool) (c : List Bool) (j : ℕ)
    (v : ZMod (Nat.fromBitsLE (modulus c) + 1)) :
    coefficientAtom modulus (pair c (pair (Term.var j).toData.toBits (residueBits v))) = residueBits (v * 1) := by
  simp only [coefficientAtom, pairFst_pair, coefficientLeaf_var, leafAccumulator, pairSnd_pair, mulMod_residueBits]

end LeanCanny.ETR.MonomialReader
