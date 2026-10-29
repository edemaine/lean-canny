/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSquareKernelCorrect

/-! # Native generation of square-system singularity queries -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SquareKernel
open LeanCanny.Encoding.Brackets

private theorem zeroWire_unary {start m : List Bool → ℕ} (hs : UnaryFn start) (hm : UnaryFn m) :
    UnaryFn (fun c => zeroWire (start c) (m c)) := hs.add hm

private theorem copyBase_unary {start m : List Bool → ℕ} (hs : UnaryFn start) (hm : UnaryFn m) :
    UnaryFn (fun c => copyBase (start c) (m c)) := (hs.add hm).add (UnaryFn.const 1)

private theorem rowBase_unary {start m : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hm : UnaryFn m) (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => rowBase (start c) (m c) (ops c)) :=
  ((copyBase_unary hs hm).add (hm.mul ((UnaryFn.const 16).mul (hs.add hlen)))).of_eq (fun _ => rfl)

private theorem rowStart_unary {start m j : List Bool → ℕ} {ops : List Bool → List Operation}
    (hs : UnaryFn start) (hm : UnaryFn m) (hj : UnaryFn j) (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => rowStart (start c) (m c) (ops c) (j c)) :=
  ((rowBase_unary hs hm hlen).add (hj.mul (((UnaryFn.const 4).mul hm).add (UnaryFn.const 3)))).of_eq (fun _ => rfl)

private theorem row_forest_range (start m : ℕ) (ops : List Operation) (outputs : ℕ → ℕ) (count : ℕ) :
    forest (rowGates start m ops outputs count) = (List.range count).flatMap (fun j =>
      forest (StraightLine.gates (rowStart start m ops j) (rowProgram start m ops outputs j))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [rowGates_succ, forest_append, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem program_encode_mem_FP {start m offset : List Bool → ℕ} {ops : List Bool → List Operation}
    {outputs : List Bool → ℕ → ℕ}
    (hs : UnaryFn start) (hm : UnaryFn m) (hoff : UnaryFn offset)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (ho : UnaryFn (fun q => outputs (pairFst q) (pairSnd q).length)) :
    (fun c => encode (StraightLine.gates (zeroWire (start c) (m c))
      (program (start c) (m c) (offset c) (ops c) (outputs c)))) ∈ FP := by
  have hz := zeroWire_unary hs hm
  have hb := copyBase_unary hs hm
  have hs' := hs.comp pairFst_mem_FP
  have hm' := hm.comp pairFst_mem_FP
  have hl' := hlen.comp pairFst_mem_FP
  have hz' := hz.comp pairFst_mem_FP
  have hb' := hb.comp pairFst_mem_FP
  have hj := UnaryFn.length pairSnd_mem_FP
  have hrow := rowStart_unary hs' hm' hj hl'
  have hv := GradientFamily.valueWire_unary hb' hs' (UnaryFn.const 0) ho hl'
  have he := GradientFamily.derivativeWire_unary (hb'.comp pairFst_mem_FP) (hs'.comp pairFst_mem_FP)
    (UnaryFn.length pairSnd_mem_FP) (ho.comp pairFst_mem_FP) (hl'.comp pairFst_mem_FP)
  have hR := KernelRow.encode_mem_FP
    (coefficient := fun _ => 0)
    (first := fun q _ => zeroWire (start (pairFst q)) (m (pairFst q)))
    (entry := fun q k => entryWire (start (pairFst q)) (m (pairFst q)) (ops (pairFst q))
      (outputs (pairFst q)) (pairSnd q).length k)
    hz' hrow hs' hm' hv hz' (constFn_mem_FP (Term.const 0).toData.toBits) (hz'.comp pairFst_mem_FP) he
  have hrows := flatMap_range_mem_FP (mem_FP_comp hR contents_mem_FP) hm.mem_FP
  have hF : (fun c => forest (rowGates (start c) (m c) (ops c) (outputs c) (m c))) ∈ FP := by
    apply mem_FP_of_eq hrows
    intro c
    simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair, contents_encode]
    rw [row_forest_range]
    rfl
  have hG := GradientFamily.encode_mem_FP hz hb hs hoff hm hlen hg
  have hzero := constantGateBits_mem_FP hz (constFn_mem_FP (Term.const 0).toData.toBits)
  have H := mem_FP_comp (appendFn_mem_FP hzero (appendFn_mem_FP (mem_FP_comp hG contents_mem_FP) hF)) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq, forest_append, forest_append]
  simp only [forest_cons, forest_nil, List.append_nil]

private theorem forest_flatMap {α : Type*} (xs : List α) (f : α → List Gate) :
    forest (xs.flatMap f) = xs.flatMap (fun a => forest (f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.flatMap_cons, forest_append, ih, List.flatMap_cons]

private theorem forest_map {α : Type*} (xs : List α) (f : α → Gate) :
    forest (xs.map f) = xs.flatMap (fun a => (f a).encode) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.map_cons, forest_cons, ih, List.flatMap_cons]

theorem constraints_forest_mem_FP {start m guardCount chart : List Bool → ℕ}
    {ops : List Bool → List Operation} {guardOutputs : List Bool → ℕ → ℕ}
    (hs : UnaryFn start) (hm : UnaryFn m) (hcount : UnaryFn guardCount) (hchart : UnaryFn chart)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hout : UnaryFn (fun q => guardOutputs (pairFst q) (pairSnd q).length)) :
    (fun c => forest (constraints (start c) (m c) (ops c) (guardCount c) (guardOutputs c) (chart c))) ∈ FP := by
  have hs' := hs.comp pairFst_mem_FP
  have hm' := hm.comp pairFst_mem_FP
  have hl' := hlen.comp pairFst_mem_FP
  have hz' := (zeroWire_unary hs hm).comp pairFst_mem_FP
  have hb' := (copyBase_unary hs hm).comp pairFst_mem_FP
  have hj := UnaryFn.length pairSnd_mem_FP
  have hrow := rowStart_unary hs' hm' hj hl'
  have hEq : UnaryFn (fun q => equationWire (start (pairFst q)) (m (pairFst q)) (ops (pairFst q)) (pairSnd q).length) :=
    ((hrow.add ((UnaryFn.const 4).mul hm')).add (UnaryFn.const 2)).of_eq (fun _ => rfl)
  have hKer := KernelRow.sumWire_unary hz' hrow hm'
  have hrows := flatMap_range_mem_FP
    (appendFn_mem_FP (zeroGateBits_mem_FP hEq) (zeroGateBits_mem_FP hKer)) hm.mem_FP
  have hValue := GradientFamily.valueWire_unary hb' hs' (UnaryFn.const 0) hout hl'
  have hguards := flatMap_range_mem_FP (zeroGateBits_mem_FP hValue) hcount.mem_FP
  have hn := constantGateBits_mem_FP (hs.add hchart) (constFn_mem_FP (Term.const 1).toData.toBits)
  apply mem_FP_of_eq (appendFn_mem_FP hn (appendFn_mem_FP hrows hguards))
  intro c
  simp only [List.length_replicate, pairFst_pair, pairSnd_pair,
    constantGateBits_encode, zeroGateBits_encode]
  simp only [constraints, forest_append, forest_flatMap, forest_map, forest_cons, forest_nil, List.append_nil]
  rfl

theorem query_encode_mem_FP {start m offset guardCount chart : List Bool → ℕ}
    {ops : List Bool → List Operation} {outputs guardOutputs : List Bool → ℕ → ℕ}
    (hs : UnaryFn start) (hm : UnaryFn m) (hoff : UnaryFn offset) (hcount : UnaryFn guardCount) (hchart : UnaryFn chart)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP)
    (ho : UnaryFn (fun q => outputs (pairFst q) (pairSnd q).length))
    (hguard : UnaryFn (fun q => guardOutputs (pairFst q) (pairSnd q).length)) :
    (fun c => encode (query (start c) (m c) (offset c) (ops c) (outputs c)
      (guardCount c) (guardOutputs c) (chart c))) ∈ FP := by
  have hprog := program_encode_mem_FP hs hm hoff hlen hg ho
  have hconstraints := constraints_forest_mem_FP hs hm hcount hchart hlen hguard
  have H := mem_FP_comp (appendFn_mem_FP (mem_FP_comp hprog contents_mem_FP) hconstraints) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode]
  rw [encode_eq_wrap, query, forest_append]

end LeanCanny.ETR.ComplexCircuit.SquareKernel
