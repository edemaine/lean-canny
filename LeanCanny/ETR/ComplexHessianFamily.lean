/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexHessianEncoding

/-! # A finite family of disjoint Hessian copies

Flattened coordinate pairs select the derivatives. A fixed stride allocates
each copy after the preceding one. The family is one acyclic program, so a
single completion realizes all selected derivatives at the same input point.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.HessianFamily
open MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical

def stride (start : ℕ) (ops : List Operation) : ℕ := 16 * (start + ops.length)
def blockStart (base start : ℕ) (ops : List Operation) (q : ℕ) : ℕ := base + q * stride start ops

def program (zWire base start m : ℕ) (ops : List Operation) : ℕ → List Operation
  | 0 => []
  | count + 1 => program zWire base start m ops count ++
      Hessian.program zWire (blockStart base start ops count) start (count / m) (count % m) ops

def gates (zWire base start m : ℕ) (ops : List Operation) (count : ℕ) : List Gate :=
  StraightLine.gates base (program zWire base start m ops count)

theorem program_length (zWire base start m : ℕ) (ops : List Operation) (count : ℕ) :
    (program zWire base start m ops count).length = count * stride start ops := by
  induction count with
  | zero => simp only [program, List.length_nil, Nat.zero_mul]
  | succ count ih =>
    simp only [program, List.length_append, Hessian.program_length, ih, stride, Nat.succ_mul]

theorem next_eq (zWire base start m : ℕ) (ops : List Operation) (count : ℕ) :
    base + (program zWire base start m ops count).length = blockStart base start ops count := by
  rw [program_length]
  rfl

theorem gates_succ (zWire base start m : ℕ) (ops : List Operation) (count : ℕ) :
    gates zWire base start m ops (count + 1) = gates zWire base start m ops count ++
      StraightLine.gates (blockStart base start ops count)
        (Hessian.program zWire (blockStart base start ops count) start (count / m) (count % m) ops) := by
  rw [gates, program, StraightLine.gates_append, next_eq]
  rfl

theorem gates_range (zWire base start m : ℕ) (ops : List Operation) (count : ℕ) :
    gates zWire base start m ops count = (List.range count).flatMap (fun q =>
      StraightLine.gates (blockStart base start ops q)
        (Hessian.program zWire (blockStart base start ops q) start (q / m) (q % m) ops)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [gates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem block_mem (zWire base start m : ℕ) (ops : List Operation) (count q : ℕ) (hq : q < count)
    (g : Gate) (hg : g ∈ StraightLine.gates (blockStart base start ops q)
      (Hessian.program zWire (blockStart base start ops q) start (q / m) (q % m) ops)) :
    g ∈ gates zWire base start m ops count := by
  rw [gates_range]
  exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hg⟩

theorem wellFormed (zWire base start m : ℕ) (ops : List Operation) (count : ℕ)
    (hz : zWire < base) (hs : start ≤ base) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed base (program zWire base start m ops count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [program, StraightLine.wellFormed_append, next_eq]
    have hb : base ≤ blockStart base start ops count := by unfold blockStart; omega
    exact ⟨ih, Hessian.wellFormed zWire _ start _ _ ops (hz.trans_le hb) (hs.trans hb) hw⟩

theorem sound (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start m : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (x env : ℕ → ℂ) (hz : env zWire = 0)
    (hx : ∀ i < start, env i = x i) (count : ℕ)
    (hg : ∀ g ∈ gates zWire base start m ops count, g.Holds env) (q : ℕ) (hq : q < count) :
    ∀ i < start + ops.length, Differential.SecondAgrees wire (q / m) (q % m) x
      (fun r => env (blockStart base start ops q + r)) i :=
  Hessian.sound wire zWire _ start _ _ ops hw hr hin x env hz hx
    (fun g h => hg g (block_mem zWire base start m ops count q hq g h))

theorem exists_completion (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start m : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (hz : zWire < base) (hs : start ≤ base)
    (x : ℕ → ℂ) (hx : x zWire = 0) (count : ℕ) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ gates zWire base start m ops count, g.Holds env) ∧
      ∀ q < count, ∀ i < start + ops.length, Differential.SecondAgrees wire (q / m) (q % m) x
        (fun r => env (blockStart base start ops q + r)) i := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x base (program zWire base start m ops count)
    (wellFormed zWire base start m ops count hz hs hw)
  exact ⟨env, hp, hg, fun q hq => sound wire zWire base start m ops hw hr hin x env ((hp _ hz).trans hx)
    (fun i hi => hp i (hi.trans_le hs)) count hg q hq⟩

theorem encode_mem_FP {zWire base start m count : List Bool → ℕ} {ops : List Bool → List Operation}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hs : UnaryFn start) (hm : UnaryFn m) (hc : UnaryFn count)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (gates (zWire c) (base c) (start c) (m c) (ops c) (count c))) ∈ FP := by
  have hz' := UnaryFn.comp (f := zWire) (g := pairFst) hz pairFst_mem_FP
  have hb' := UnaryFn.comp (f := base) (g := pairFst) hb pairFst_mem_FP
  have hs' := UnaryFn.comp (f := start) (g := pairFst) hs pairFst_mem_FP
  have hm' := UnaryFn.comp (f := m) (g := pairFst) hm pairFst_mem_FP
  have hl' := UnaryFn.comp (f := fun c => (ops c).length) (g := pairFst) hlen pairFst_mem_FP
  have hq := UnaryFn.length pairSnd_mem_FP
  have hblock := hb'.add (hq.mul ((UnaryFn.const 16).mul (hs'.add hl')))
  have hcopy := Hessian.program_encode_mem_FP hz' hblock hs' (hq.div hm') (hq.mod hm')
    (mem_FP_comp pairFst_mem_FP hg)
  have h := mem_FP_comp (flatMap_range_mem_FP (mem_FP_comp hcopy contents_mem_FP) hc.mem_FP) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair, contents_encode]
  rw [encode_eq_wrap, gates_range]
  congr 1
  induction count c with
  | zero => rfl
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, forest_append, ih]
    rfl

theorem source_encode_mem_FP {zWire base m count : List Bool → ℕ} {source : List Bool → List Bool}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hm : UnaryFn m) (hc : UnaryFn count) (ht : source ∈ FP) :
    (fun c => encode (gates (zWire c) (base c) (TermView.term (source c)).toData.size (m c)
      (Source.program (TermView.term (source c)).toData.size (TermView.term (source c))) (count c))) ∈ FP := by
  have hs : UnaryFn (fun c => (TermView.term (source c)).toData.size) :=
    (UnaryFn.length (mem_FP_comp ht TermView.normalize_mem_FP)).of_eq
      (fun c => by simp only [Function.comp_apply, TermView.normalize_eq_term, Data.length_toBits])
  have hn := UnaryFn.comp (f := Source.Machine.nextIndex) (g := source) Source.Machine.nextIndex_unary ht
  have hlen : UnaryFn (fun c => (Source.program (TermView.term (source c)).toData.size (TermView.term (source c))).length) :=
    (hn.sub hs).of_eq (fun c => by
      simp only [Source.Machine.nextIndex_eq, Nat.add_sub_cancel_left, Source.program_length])
  apply encode_mem_FP hz hb hs hm hc hlen
  simpa only [Source.gates_eq] using Source.encoded_gates_mem_FP ht

end LeanCanny.ETR.ComplexCircuit.HessianFamily
