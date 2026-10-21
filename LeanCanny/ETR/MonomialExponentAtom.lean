/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderEncoding

/-! # FP leaf accumulation for a selected variable's exponent -/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def leafTerm (p : List Bool) : List Bool := pairFst (pairSnd p)
def leafAccumulator (p : List Bool) : List Bool := pairSnd (pairSnd p)
def variableCode (p : List Bool) : List Bool := BinaryNatCode.encode (Codec.unaryValue (NNF.second (leafTerm p)))

theorem leafTerm_mem_FP : leafTerm ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem leafAccumulator_mem_FP : leafAccumulator ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem variableCode_mem_FP : variableCode ∈ FP := by
  have hp := mem_FP_comp leafTerm_mem_FP NNF.second_mem_FP
  have h := bits_mem_FP (Codec.unaryValue_unary.comp hp)
  refine mem_FP_of_eq (g := variableCode) h ?_
  intro p
  simp only [variableCode, BinaryNatCode.encode, Function.comp_apply]

def exponentLeaf (varIndex : List Bool → List Bool) (p : List Bool) : List Bool :=
  if NNF.HasOne 1 (leafTerm p) ∧ BinaryNat.normalize (varIndex (pairFst p)) = variableCode p then [true] else []

def exponentAtom (varIndex : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.add (pair (leafAccumulator p) (exponentLeaf varIndex p))

theorem exponentLeaf_mem_FP {varIndex : List Bool → List Bool} (hv : varIndex ∈ FP) : exponentLeaf varIndex ∈ FP := by
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP hv) BinaryNat.normalize_mem_FP
  have hp := ((NNF.hasOne_fppred 1).comp leafTerm_mem_FP).and (stringEq_fppred hi variableCode_mem_FP)
  have h := hp.ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  exact mem_FP_of_eq (g := exponentLeaf varIndex) h (fun _ => rfl)

theorem exponentAtom_mem_FP {varIndex : List Bool → List Bool} (hv : varIndex ∈ FP) : exponentAtom varIndex ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair leafAccumulator_mem_FP (exponentLeaf_mem_FP hv)) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := exponentAtom varIndex) h ?_
  intro p
  simp only [exponentAtom, Function.comp_apply]

theorem exponentLeaf_const (varIndex : List Bool → List Bool) (c v : List Bool) (z : ℤ) :
    exponentLeaf varIndex (pair c (pair (Term.const z).toData.toBits v)) = [] := by
  simp [exponentLeaf, leafTerm, NNF.hasOne_toBits, NNF.one, Term.toData, Codec.unary]

theorem exponentLeaf_var (varIndex : List Bool → List Bool) (c v : List Bool) (j : ℕ) :
    exponentLeaf varIndex (pair c (pair (Term.var j).toData.toBits v)) =
      BinaryNatCode.encode (if Nat.fromBitsLE (varIndex c) = j then 1 else 0) := by
  have heq : BinaryNat.normalize (varIndex c) = BinaryNatCode.encode j ↔ Nat.fromBitsLE (varIndex c) = j := by
    rw [BinaryNat.normalize_eq_bits]
    exact BinaryNatCode.encode_injective.eq_iff
  have htag : NNF.HasOne 1 (Term.var j).toData.toBits := by
    rw [NNF.hasOne_toBits]
    exact ⟨Codec.unary j, rfl⟩
  simp only [exponentLeaf, leafTerm, pairFst_pair, pairSnd_pair, htag, true_and]
  simp only [variableCode, leafTerm, pairFst_pair, pairSnd_pair, NNF.second,
    Term.toData, remainingChildren_toBits, firstChild_toBits, Codec.unaryValue_toBits]
  simp only [heq]
  split_ifs <;> rfl

theorem exponentAtom_const (varIndex : List Bool → List Bool) (c : List Bool) (z : ℤ) (v : Multiplicative ℕ) :
    exponentAtom varIndex (pair c (pair (Term.const z).toData.toBits (BinaryNatCode.encode v.toAdd))) =
      BinaryNatCode.encode (v * Multiplicative.ofAdd 0).toAdd := by
  simp only [exponentAtom, exponentLeaf_const, leafAccumulator, pairSnd_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show Nat.fromBitsLE [] = 0 from rfl, Nat.add_zero, toAdd_mul,
    toAdd_ofAdd]

theorem exponentAtom_var (varIndex : List Bool → List Bool) (c : List Bool) (j : ℕ) (v : Multiplicative ℕ) :
    exponentAtom varIndex (pair c (pair (Term.var j).toData.toBits (BinaryNatCode.encode v.toAdd))) =
      BinaryNatCode.encode (v * Multiplicative.ofAdd (if Nat.fromBitsLE (varIndex c) = j then 1 else 0)).toAdd := by
  simp only [exponentAtom, exponentLeaf_var, leafAccumulator, pairSnd_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, toAdd_mul, toAdd_ofAdd]

theorem exponent_step_value_le (i : ℕ) (s : State (Multiplicative ℕ)) :
    (step (fun _ => Multiplicative.ofAdd 0) (fun j => Multiplicative.ofAdd (if i = j then 1 else 0)) s).value.toAdd ≤
      s.value.toAdd + 1 := by
  rcases s with ⟨todo, v⟩
  cases todo with
  | nil => simp [step]
  | cons q rest =>
    rcases q with ⟨t, r⟩
    cases t <;> simp only [step]
    · simp
    · simp only [toAdd_mul, toAdd_ofAdd]; split_ifs <;> omega
    · split_ifs <;> simp
    · simp

theorem exponent_iterate_value_le (i : ℕ) (s : State (Multiplicative ℕ)) (k : ℕ) :
    (((step (fun _ => Multiplicative.ofAdd 0) (fun j => Multiplicative.ofAdd (if i = j then 1 else 0)))^[k]) s).value.toAdd ≤
      s.value.toAdd + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (exponent_step_value_le _ _).trans (by omega)

end LeanCanny.ETR.MonomialReader
