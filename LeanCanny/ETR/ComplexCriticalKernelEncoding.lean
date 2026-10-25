/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelCorrect

/-! # Native generation of the complete affine critical-kernel circuit

The generator includes the original source, all initialized derivative copies,
kernel-row arithmetic, normalization, and zero tests. Integer direction entries
are copied from their literal writer. Every wire calculation and loop is unary.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CriticalKernel
open LeanCanny.Encoding.Brackets

theorem copyBase_unary {start m : List Bool → ℕ} (hs : UnaryFn start) (hm : UnaryFn m) :
    UnaryFn (fun c => copyBase (start c) (m c)) :=
  ((hs.add hm).add (UnaryFn.const 1)).of_eq (fun _ => rfl)

theorem rowsBase_unary {start m : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hm : UnaryFn m) (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => rowsBase (start c) (m c) (ops c)) :=
  ((copyBase_unary hs hm).add ((hm.mul hm).mul ((UnaryFn.const 16).mul (hs.add hlen)))).of_eq (fun _ => rfl)

theorem rowStart_unary {start m j : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hm : UnaryFn m) (hlen : UnaryFn (fun c => (ops c).length)) (hj : UnaryFn j) :
    UnaryFn (fun c => rowStart (start c) (m c) (ops c) (j c)) :=
  ((rowsBase_unary hs hm hlen).add (hj.mul (((UnaryFn.const 4).mul hm).add (UnaryFn.const 3)))).of_eq (fun _ => rfl)

theorem jetWire_unary {start m out j k slot : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hm : UnaryFn m) (hlen : UnaryFn (fun c => (ops c).length))
    (ho : UnaryFn out) (hj : UnaryFn j) (hk : UnaryFn k) (hslot : UnaryFn slot) :
    UnaryFn (fun c => jetWire (start c) (m c) (ops c) (out c) (j c) (k c) (slot c)) :=
  ((((copyBase_unary hs hm).add (((hj.mul hm).add hk).mul
    ((UnaryFn.const 16).mul (hs.add hlen)))).add ((UnaryFn.const 16).mul ho)).add hslot).of_eq (fun _ => rfl)

theorem row_encode_mem_FP {start m out j : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} (hs : UnaryFn start) (hm : UnaryFn m)
    (hlen : UnaryFn (fun c => (ops c).length)) (ho : UnaryFn out) (hj : UnaryFn j)
    (hc : (fun c => (Term.const (coefficient (v c) (j c))).toData.toBits) ∈ FP) :
    (fun c => encode (StraightLine.gates (rowStart (start c) (m c) (ops c) (j c))
      (row (start c) (m c) (ops c) (out c) (v c) (j c)))) ∈ FP := by
  have hvalue := UnaryFn.ite (FPPred.eq hj (UnaryFn.const 0))
    (jetWire_unary hs hm hlen ho (UnaryFn.const 0) (UnaryFn.const 0) (UnaryFn.const 0))
    (jetWire_unary hs hm hlen ho (UnaryFn.const 0) hj (UnaryFn.const 3))
  have hbase := jetWire_unary hs hm hlen ho (UnaryFn.const 0) (UnaryFn.const 0) (UnaryFn.const 3)
  have hs' := UnaryFn.comp (f := start) (g := pairFst) hs pairFst_mem_FP
  have hm' := UnaryFn.comp (f := m) (g := pairFst) hm pairFst_mem_FP
  have hl' := UnaryFn.comp (f := fun c => (ops c).length) (g := pairFst) hlen pairFst_mem_FP
  have ho' := UnaryFn.comp (f := out) (g := pairFst) ho pairFst_mem_FP
  have hj' := UnaryFn.comp (f := j) (g := pairFst) hj pairFst_mem_FP
  have hk := UnaryFn.length pairSnd_mem_FP
  have hfirst := jetWire_unary hs' hm' hl' ho' (UnaryFn.const 0) hk (UnaryFn.const 15)
  have hentry := UnaryFn.ite (FPPred.eq hj' (UnaryFn.const 0))
    (jetWire_unary hs' hm' hl' ho' (UnaryFn.const 0) hk (UnaryFn.const 3))
    (jetWire_unary hs' hm' hl' ho' hj' hk (UnaryFn.const 15))
  exact KernelRow.encode_mem_FP (hs.add hm) (rowStart_unary hs hm hlen hj) hs hm hvalue hbase hc hfirst hentry

theorem coefficient_literal_mem_FP {j : List Bool → ℕ} {v : List Bool → ℕ → ℤ} (hj : UnaryFn j)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => (Term.const (coefficient (v c) (j c))).toData.toBits) ∈ FP := by
  have hneg := mem_FP_comp (mem_FP_pair id_mem_FP ((hj.sub (UnaryFn.const 1)).mem_FP)) hv
  have h := (FPPred.eq hj (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP (Term.const 0).toData.toBits) hneg
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, coefficient]
  split_ifs <;> rfl

private theorem forest_flatMap {α : Type*} (xs : List α) (f : α → List Gate) :
    forest (xs.flatMap f) = xs.flatMap (fun a => forest (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.flatMap_cons, forest_append, ih, List.flatMap_cons]

theorem query_encode_mem_FP {start m out chart : List Bool → ℕ} {ops : List Bool → List Operation}
    {v : List Bool → ℕ → ℤ} (hs : UnaryFn start) (hm : UnaryFn m) (ho : UnaryFn out) (hi : UnaryFn chart)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (hv : (fun p => (Term.const (-v (pairFst p) (pairSnd p).length)).toData.toBits) ∈ FP) :
    (fun c => encode (query (start c) (m c) (ops c) (out c) (v c) (chart c))) ∈ FP := by
  have hz := hs.add hm
  have hcopies := HessianFamily.encode_mem_FP hz (copyBase_unary hs hm) hs hm (hm.mul hm) hlen hg
  have hs' := UnaryFn.comp (f := start) (g := pairFst) hs pairFst_mem_FP
  have hm' := UnaryFn.comp (f := m) (g := pairFst) hm pairFst_mem_FP
  have hl' := UnaryFn.comp (f := fun c => (ops c).length) (g := pairFst) hlen pairFst_mem_FP
  have ho' := UnaryFn.comp (f := out) (g := pairFst) ho pairFst_mem_FP
  have hj := UnaryFn.length pairSnd_mem_FP
  have hstrip := mem_FP_pair (mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have hv' : (fun p => (Term.const (-v (pairFst (pairFst p)) (pairSnd p).length)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp hstrip hv) (fun p => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])
  have hc := coefficient_literal_mem_FP (v := fun p => v (pairFst p)) hj hv'
  have hrow := row_encode_mem_FP (v := fun p => v (pairFst p)) hs' hm' hl' ho' hj hc
  have hrows := flatMap_range_mem_FP (mem_FP_comp hrow contents_mem_FP) hm.mem_FP
  have hzero := constantGateBits_mem_FP hz (constFn_mem_FP (Term.const 0).toData.toBits)
  have hnormal := constantGateBits_mem_FP (hs.add hi) (constFn_mem_FP (Term.const 1).toData.toBits)
  have hrstart := rowStart_unary hs' hm' hl' hj
  have hsum := zeroGateBits_mem_FP (KernelRow.sumWire_unary (hs'.add hm') hrstart hm')
  have hcrit := zeroGateBits_mem_FP ((hrstart.add ((UnaryFn.const 4).mul hm')).add (UnaryFn.const 2))
  have hconstraints := flatMap_range_mem_FP (appendFn_mem_FP hsum hcrit) hm.mem_FP
  have h := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP hzero (mem_FP_comp hcopies contents_mem_FP)) hrows) hnormal)
      hconstraints) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair,
    contents_encode, constantGateBits_encode, zeroGateBits_encode]
  rw [encode_eq_wrap]
  simp only [query, constraints, gates_eq, forest_append, forest_cons, forest_nil,
    forest_flatMap, List.append_nil, List.append_assoc, KernelRow.criticalWire]
  rfl

end LeanCanny.ETR.ComplexCircuit.CriticalKernel
