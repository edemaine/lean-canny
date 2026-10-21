/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeZeroBounds
public import LeanCanny.Tactic.PolyTime

/-! # Polynomial-time writing of the sparse zero-source tube

Polynomially many short constraint terms are serialized by a range loop.
The existing sum-of-squares writer combines them without distributing any
products. Arity and active-mask fields are total FP inputs.
-/

@[expose] public section

namespace LeanCanny.ETR.Term


theorem varCode_mem_FP {i : List Bool → ℕ} (hi : UnaryFn i) :
    (fun c => (Term.var (i c)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (variableBits_mem_FP hi) (fun c => variableBits_eq (i c))

theorem addCode_mem_FP {a b : List Bool → Term}
    (ha : (fun c => (a c).toData.toBits) ∈ FP) (hb : (fun c => (b c).toData.toBits) ∈ FP) :
    (fun c => (Term.add (a c) (b c)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 ha hb) (fun c => (add_toBits (a c) (b c)).symm)

theorem mulCode_mem_FP {a b : List Bool → Term}
    (ha : (fun c => (a c).toData.toBits) ∈ FP) (hb : (fun c => (b c).toData.toBits) ∈ FP) :
    (fun c => (Term.mul (a c) (b c)).toData.toBits) ∈ FP :=
  mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 ha hb) (fun c => (mul_toBits (a c) (b c)).symm)

theorem squareCode_mem_FP {a : List Bool → Term} (ha : (fun c => (a c).toData.toBits) ∈ FP) :
    (fun c => (a c).square.toData.toBits) ∈ FP := mulCode_mem_FP ha ha

end LeanCanny.ETR.Term

namespace LeanCanny.ETR.SumSquares

open LeanCanny.Encoding.Brackets

theorem accumulate_range_mem_FP (N : List Bool → ℕ) (E : List Bool → ℕ → Term) (hN : UnaryFn N)
    (hr : (fun z => (E (pairFst z) (pairSnd z).length).toData.toBits) ∈ FP) :
    (fun c => (accumulate ((List.range (N c)).map (E c)) (.const 0)).toData.toBits) ∈ FP := by
  have hf := flatMap_range_mem_FP hr hN
  have h := mem_FP_comp (mem_FP_comp hf wrap_mem_FP) collapse_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]
  have hl : wrap ((List.range (N c)).flatMap (fun j => (E c j).toData.toBits)) = listBits ((List.range (N c)).map (E c)) := by
    simp only [listBits, Data.toBits_l, List.map_map, Function.comp_def, List.flatMap, wrap]
  rw [hl, collapse_listBits]

end LeanCanny.ETR.SumSquares

namespace LeanCanny.ETR.TubeZero

open LeanCanny.Encoding
open TubeEncoding

theorem constraintCount_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun c => constraintCount (n c)) :=
  (UnaryFn.const 2).add (hn.mul (UnaryFn.const 2))

theorem oneMinusEpsilon_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun c => (oneMinusEpsilon (n c)).toData.toBits) ∈ FP :=
  Term.addCode_mem_FP (constFn_mem_FP (Term.const 1).toData.toBits)
    (Term.mulCode_mem_FP (constFn_mem_FP (Term.const (-1)).toData.toBits)
      (Term.varCode_mem_FP ((hn.add (constraintCount_unary hn)).add (UnaryFn.const 1))))

theorem constraint_mem_FP {n j : List Bool → ℕ} (hn : UnaryFn n) (hj : UnaryFn j) :
    (fun c => (constraint (n c) (j c)).toData.toBits) ∈ FP := by
  have hx := Term.varCode_mem_FP ((hj.sub (UnaryFn.const 2)).div (UnaryFn.const 2))
  have hs := Term.varCode_mem_FP (hn.add hj)
  have he := oneMinusEpsilon_mem_FP hn
  have hlo := Term.addCode_mem_FP (Term.addCode_mem_FP hx he) hs
  have hhi := Term.addCode_mem_FP (Term.addCode_mem_FP he
    (Term.mulCode_mem_FP (constFn_mem_FP (Term.const (-1)).toData.toBits) hx)) hs
  have h := (FPPred.lt hj (UnaryFn.const 2)).ite_mem_FP hs
    ((FPPred.eq (hj.mod (UnaryFn.const 2)) (UnaryFn.const 0)).ite_mem_FP hlo hhi)
  apply mem_FP_of_eq h
  intro c
  unfold constraint
  split_ifs <;> rfl

theorem radius_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) :
    (fun c => (radius (n c)).toData.toBits) ∈ FP := by
  have hr := SumSquares.accumulate_range_mem_FP (fun c => constraintCount (n c)) (fun c j => Term.var (n c + j))
    (constraintCount_unary hn) (Term.varCode_mem_FP (hn.lift.add UnaryFn.index))
  have hd := Term.varCode_mem_FP ((hn.add (constraintCount_unary hn)).add (UnaryFn.const 2))
  have h := Term.addCode_mem_FP hr (Term.mulCode_mem_FP (constFn_mem_FP (Term.const (-1)).toData.toBits)
    (Term.squareCode_mem_FP hd))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem active_accumulate_mem_FP {n : List Bool → ℕ} {bits : List Bool → List Bool}
    (hn : UnaryFn n) (hb : bits ∈ FP) :
    (fun c => (SumSquares.accumulate (activeTerms (n c) (bits c)) (.const 0)).toData.toBits) ∈ FP := by
  let E := fun c j => if (bits c)[j]?.getD false then constraint (n c) j else Term.const 0
  have htest := FPPred.getBit (mem_FP_comp pairFst_mem_FP hb) UnaryFn.index
  have hr := htest.ite_mem_FP (constraint_mem_FP hn.lift UnaryFn.index) (constFn_mem_FP (Term.const 0).toData.toBits)
  have hread : (fun z => (E (pairFst z) (pairSnd z).length).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq hr
    intro z
    dsimp only [E, Function.comp_apply]
    split_ifs <;> rfl
  exact SumSquares.accumulate_range_mem_FP (fun c => constraintCount (n c)) E (constraintCount_unary hn) hread

def write (n : List Bool → ℕ) (bits : List Bool → List Bool) (c : List Bool) : List Bool := (term (n c) (bits c)).toData.toBits

theorem write_mem_FP {n : List Bool → ℕ} {bits : List Bool → List Bool} (hn : UnaryFn n) (hb : bits ∈ FP) : write n bits ∈ FP := by
  have ha := Term.varCode_mem_FP (hn.add (constraintCount_unary hn))
  have h := Term.addCode_mem_FP (Term.addCode_mem_FP (Term.squareCode_mem_FP (radius_mem_FP hn))
    (active_accumulate_mem_FP hn hb)) (Term.mulCode_mem_FP (constFn_mem_FP (Term.const (-1)).toData.toBits) ha)
  exact mem_FP_of_eq h (fun _ => rfl)

end LeanCanny.ETR.TubeZero
