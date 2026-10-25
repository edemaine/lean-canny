/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInfinityCorrect
public import LeanCanny.ETR.ComplexPowerEncoding
public import LeanCanny.ETR.NumericLiteralFP

/-! # Native polynomial-time generation of infinity-chart circuits

A unary range concatenates the independently encoded coordinate blocks. Every
wire index is polynomial in the dimension and literal exponent length; integer
direction coordinates are copied from their binary literal writer.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Infinity
open LeanCanny.Encoding.Brackets

theorem sumWire_eq_if (m : ℕ) (bits : List Bool) (j : ℕ) :
    sumWire m bits j = if j = 0 then m else powerWire m bits (j - 1) + 2 := by
  cases j <;> simp [sumWire]

theorem start_unary {m j : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (hj : UnaryFn j) (he : bits ∈ FP) :
    UnaryFn (fun c => start (m c) (bits c) (j c)) :=
  ((hm.add (UnaryFn.const 1)).add
    (hj.mul (((UnaryFn.const 2).mul (UnaryFn.length he)).add (UnaryFn.const 6)))).of_eq (fun _ => rfl)

theorem powerWire_unary {m j : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (hj : UnaryFn j) (he : bits ∈ FP) :
    UnaryFn (fun c => powerWire (m c) (bits c) (j c)) :=
  ((start_unary hm hj he).add ((UnaryFn.const 2).mul (UnaryFn.length he))).of_eq (fun _ => rfl)

theorem sumWire_unary {m j : List Bool → ℕ} {bits : List Bool → List Bool}
    (hm : UnaryFn m) (hj : UnaryFn j) (he : bits ∈ FP) :
    UnaryFn (fun c => sumWire (m c) (bits c) (j c)) := by
  have h := UnaryFn.ite (FPPred.eq hj (UnaryFn.const 0)) hm
    ((powerWire_unary hm (hj.sub (UnaryFn.const 1)) he).add (UnaryFn.const 2))
  exact h.of_eq (fun c => (sumWire_eq_if (m c) (bits c) (j c)).symm)

theorem block_forest_mem_FP {m j : List Bool → ℕ} {bits : List Bool → List Bool}
    {v : List Bool → ℕ → ℤ} (hm : UnaryFn m) (hj : UnaryFn j) (he : bits ∈ FP)
    (hv : (fun c => (Term.const (-(v c (j c)))).toData.toBits) ∈ FP) :
    (fun c => forest (blockGates (m c) (bits c) (v c) (j c))) ∈ FP := by
  have hp := Power.forest_mem_FP hj (start_unary hm hj he) he
  have hw := powerWire_unary hm hj he
  have hb := powerWire_unary hm (UnaryFn.const 0) he
  have hmul := arithmeticGateBits_mem_FP 2 (hw.add (UnaryFn.const 1)) hw hj
  have hsum := arithmeticGateBits_mem_FP 1 (sumWire_unary hm (hj.add (UnaryFn.const 1)) he)
    (sumWire_unary hm hj he) (hw.add (UnaryFn.const 1))
  have hc := constantGateBits_mem_FP (hw.add (UnaryFn.const 3)) hv
  have hprod := arithmeticGateBits_mem_FP 2 (hw.add (UnaryFn.const 4)) (hw.add (UnaryFn.const 3)) hb
  have hd := arithmeticGateBits_mem_FP 1 (hw.add (UnaryFn.const 5)) hw (hw.add (UnaryFn.const 4))
  have h := appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP hp hmul) hsum) hc) hprod) hd
  apply mem_FP_of_eq h
  intro c
  simp only [mulGateBits_encode, addGateBits_encode, constantGateBits_encode, blockGates,
    forest_append, forest_cons, forest_nil, List.append_nil, List.append_assoc, differenceWire]

theorem forest_flatMap {α : Type*} (xs : List α) (f : α → List Gate) :
    forest (xs.flatMap f) = xs.flatMap (fun i => forest (f i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [List.flatMap_cons, forest_append, ih, List.flatMap_cons]

theorem forest_map {α : Type*} (xs : List α) (f : α → Gate) :
    forest (xs.map f) = xs.flatMap (fun i => (f i).encode) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => rw [List.map_cons, forest_cons, ih, List.flatMap_cons]

theorem prefixGates_range (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) :
    prefixGates m bits v k = [.constant m 0] ++ (List.range k).flatMap (blockGates m bits v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prefixGates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem encode_mem_FP {m i : List Bool → ℕ} {bits : List Bool → List Bool} {v : List Bool → ℕ → ℤ}
    (hm : UnaryFn m) (hi : UnaryFn i) (he : bits ∈ FP)
    (hv : (fun q => (Term.const (-(v (pairFst q) (pairSnd q).length))).toData.toBits) ∈ FP) :
    (fun c => encode (query (m c) (bits c) (v c) (i c))) ∈ FP := by
  have hmp := UnaryFn.comp (f := m) (g := pairFst) hm pairFst_mem_FP
  have hep := mem_FP_comp (f := pairFst) (g := bits) pairFst_mem_FP he
  have hjp := UnaryFn.length pairSnd_mem_FP
  have hblock := block_forest_mem_FP (v := fun q => v (pairFst q)) hmp hjp hep hv
  have hrange := flatMap_range_mem_FP hblock hm.mem_FP
  have hn := constantGateBits_mem_FP hi (constFn_mem_FP (Term.const 1).toData.toBits)
  have hz := constantGateBits_mem_FP hm (constFn_mem_FP (Term.const 0).toData.toBits)
  have hsum := zeroGateBits_mem_FP (sumWire_unary hm hm he)
  have hd := zeroGateBits_mem_FP
    ((powerWire_unary hmp (hjp.add (UnaryFn.const 1)) hep).add (UnaryFn.const 5))
  have hdiff := flatMap_range_mem_FP hd (hm.sub (UnaryFn.const 1)).mem_FP
  have h := mem_FP_comp (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP hn (appendFn_mem_FP hz hrange)) hsum) hdiff) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair,
    constantGateBits_encode, zeroGateBits_encode]
  rw [encode_eq_wrap]
  simp only [query, forest_append, prefixGates_range, forest_cons, forest_nil, List.append_nil,
    forest_flatMap, forest_map, List.append_assoc, differenceWire]

end LeanCanny.ETR.ComplexCircuit.Infinity
