/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRealConstraints
public import LeanCanny.ETR.ComplexCircuitShift

/-! # Real parent-circuit constraints beside a free coordinate block

Parent gates and their real-input guards use a later witness region. Linear
links identify the frozen source inputs with parent coordinates, including
zero extension beyond the parent dimension. The formula has native writers
and does not constrain the free block or kernel auxiliaries accidentally.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.FrozenParentConstraint
open LeanCanny.Computation LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def point (count base : ℕ) (x : ℕ → ℝ) : Fin count → ℝ := fun i => x (2 * (base + i.val))
def parentEnv (base : ℕ) (x : ℕ → ℝ) (i : ℕ) : ℂ := complexEnv x (base + i)
def guards (frame base : ℕ) : List Term := (List.range frame).map (fun i => imagWire (base + i))
def link (count free base i : ℕ) : Term :=
  difference (.var (free + i)) (if i < count then realWire (base + i) else .const 0)
def links (count free inputs base : ℕ) : List Term := (List.range inputs).map (link count free base)
def formula (count frame free inputs base : ℕ) (prior : List Gate) : Formula :=
  .eqZero (SumSquares.accumulate
    (equations (prior.map (Gate.shift base)) ++ guards frame base ++ links count free inputs base) (.const 0))

theorem link_eval (count free base i : ℕ) (x : ℕ → ℝ) :
    (link count free base i).eval x = x (free + i) - Formula.extend (point count base x) i := by
  by_cases hi : i < count <;> simp [link, eval_difference, hi, Term.eval, realWire, Formula.extend, point]

theorem holds_iff (count frame free inputs base : ℕ) (prior : List Gate) (x : ℕ → ℝ) :
    (formula count frame free inputs base prior).Holds x ↔
      (∀ g ∈ prior, g.Holds (parentEnv base x)) ∧
        (∀ i < frame, (parentEnv base x i).im = 0) ∧
          ∀ i < inputs, x (free + i) = Formula.extend (point count base x) i := by
  simp only [formula, Formula.Holds, SumSquares.accumulate_zero_iff, List.forall_mem_append]
  rw [equations_iff]
  simp only [List.forall_mem_map, Gate.shift_holds, guards, links, List.mem_range, link_eval,
    sub_eq_zero, imagWire, Term.eval, parentEnv, complexEnv, and_assoc]
  rfl

private theorem range_bits_FP {count : List Bool → ℕ} {f : List Bool → ℕ → Term}
    (hn : UnaryFn count) (hf : (fun q => (f (pairFst q) (pairSnd q).length).toData.toBits) ∈ FP) :
    (fun c => SumSquares.listBits ((List.range (count c)).map (f c))) ∈ FP := by
  have h := mem_FP_comp (flatMap_range_mem_FP hf hn.mem_FP) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    SumSquares.listBits, Data.toBits_l, List.map_map, List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def]
  rfl

theorem guards_bits_FP {frame base : List Bool → ℕ} (hf : UnaryFn frame) (hb : UnaryFn base) :
    (fun c => SumSquares.listBits (guards (frame c) (base c))) ∈ FP := by
  apply range_bits_FP hf
  exact mem_FP_of_eq (imagBits_mem_FP ((hb.comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP)))
    (fun q => imagBits_toBits _)

theorem links_bits_FP {count free inputs base : List Bool → ℕ}
    (hn : UnaryFn count) (hd : UnaryFn free) (hi : UnaryFn inputs) (hb : UnaryFn base) :
    (fun c => SumSquares.listBits (links (count c) (free c) (inputs c) (base c))) ∈ FP := by
  have hj := UnaryFn.length pairSnd_mem_FP
  have hright := (FPPred.lt hj (hn.comp pairFst_mem_FP)).ite_mem_FP
    (realBits_mem_FP ((hb.comp pairFst_mem_FP).add hj)) (constFn_mem_FP (Term.const 0).toData.toBits)
  have hleft := Term.variableBits_mem_FP ((hd.comp pairFst_mem_FP).add hj)
  apply range_bits_FP hi
  exact mem_FP_of_eq (differenceBits_mem_FP hleft hright) (fun q => by
    unfold link
    split_ifs <;> simp only [realBits_toBits, Term.variableBits_eq, differenceBits_toBits])

def bits (count frame free inputs base : ℕ) (prior : List Bool) : List Bool :=
  EquationList.toSingleEquation (wrap
    (contents (ComplexCircuit.compile (WireShift.run (pair (List.replicate base true) prior))) ++
      contents (SumSquares.listBits (guards frame base)) ++ contents (SumSquares.listBits (links count free inputs base))))

theorem bits_encode (count frame free inputs base : ℕ) (prior : List Gate) :
    bits count frame free inputs base (encode prior) = (formula count frame free inputs base prior).encode := by
  rw [bits, WireShift.run_encode, ComplexCircuit.compile_encode]
  simp only [SumSquares.contents_listBits]
  have he (ts : List Term) : SumSquares.listBits ts = wrap (SumSquares.forest ts) := by
    simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, List.map_map, Function.comp_def]
    rfl
  rw [← real_forest_append, ← real_forest_append, ← he, EquationList.toSingleEquation_listBits]
  rfl

attribute [local irreducible] WireShift.run ComplexCircuit.compile contents wrap pair pairFst pairSnd

theorem bits_FP {count frame free inputs base : List Bool → ℕ} {prior : List Bool → List Bool}
    (hn : UnaryFn count) (hf : UnaryFn frame) (hd : UnaryFn free) (hi : UnaryFn inputs) (hb : UnaryFn base)
    (hg : prior ∈ FP) : (fun c => bits (count c) (frame c) (free c) (inputs c) (base c) (prior c)) ∈ FP := by
  unfold bits
  have hs := mem_FP_comp (mem_FP_pair hb.mem_FP hg) WireShift.run_mem_FP
  have hgate := mem_FP_comp (mem_FP_comp hs ComplexCircuit.compile_mem_FP) contents_mem_FP
  have hguard := mem_FP_comp (guards_bits_FP hf hb) contents_mem_FP
  have hlink := mem_FP_comp (links_bits_FP hn hd hi hb) contents_mem_FP
  have hseq : (fun c => contents (ComplexCircuit.compile (WireShift.run (pair (List.replicate (base c) true) (prior c)))) ++
      contents (SumSquares.listBits (guards (frame c) (base c))) ++
      contents (SumSquares.listBits (links (count c) (free c) (inputs c) (base c)))) ∈ FP :=
    appendFn_mem_FP (appendFn_mem_FP hgate hguard) hlink
  exact mem_FP_comp (mem_FP_comp hseq wrap_mem_FP) EquationList.toSingleEquation_mem_FP

theorem formula_FP {count frame free inputs base : List Bool → ℕ} {prior : List Bool → List Gate}
    (hn : UnaryFn count) (hf : UnaryFn frame) (hd : UnaryFn free) (hi : UnaryFn inputs) (hb : UnaryFn base)
    (hg : (fun c => encode (prior c)) ∈ FP) :
    (fun c => (formula (count c) (frame c) (free c) (inputs c) (base c) (prior c)).encode) ∈ FP :=
  mem_FP_of_eq (bits_FP hn hf hd hi hb hg)
    (fun c => bits_encode (count c) (frame c) (free c) (inputs c) (base c) (prior c))

noncomputable def assignment {count free : ℕ} (base : ℕ) (y : Fin free → ℝ) (parent : Fin count → ℝ)
    (env : ℕ → ℂ) (i : ℕ) : ℝ :=
  if hi : i < free then y ⟨i, hi⟩ else if 2 * base ≤ i then realEnv env (i - 2 * base)
    else Formula.extend parent (i - free)

theorem assignment_free {count free : ℕ} (base : ℕ) (y : Fin free → ℝ) (parent : Fin count → ℝ)
    (env : ℕ → ℂ) (i : Fin free) : assignment base y parent env i.val = y i := by
  simp only [assignment, i.isLt, dite_true, Fin.eta]

theorem assignment_frozen {count free : ℕ} (base inputs : ℕ) (y : Fin free → ℝ) (parent : Fin count → ℝ)
    (env : ℕ → ℂ) (hb : free + inputs ≤ base) (i : ℕ) (hi : i < inputs) :
    assignment base y parent env (free + i) = Formula.extend parent i := by
  have hfree : ¬free + i < free := by omega
  have hbase : ¬2 * base ≤ free + i := by omega
  simp only [assignment, hfree, dite_false, hbase, ite_false, Nat.add_sub_cancel_left]

theorem assignment_parentEnv {count free : ℕ} (base : ℕ) (y : Fin free → ℝ) (parent : Fin count → ℝ)
    (env : ℕ → ℂ) (hb : free ≤ base) : parentEnv base (assignment base y parent env) = env := by
  funext i
  have hr : ¬2 * (base + i) < free := by omega
  have hi : ¬2 * (base + i) + 1 < free := by omega
  have hbr : 2 * base ≤ 2 * (base + i) := by omega
  have hbi : 2 * base ≤ 2 * (base + i) + 1 := by omega
  have hsr : 2 * (base + i) - 2 * base = 2 * i := by omega
  have hsi : 2 * (base + i) + 1 - 2 * base = 2 * i + 1 := by omega
  apply Complex.ext
  · simp only [parentEnv, complexEnv, assignment, hr, dite_false, hbr, ite_true, hsr, realEnv_even]
  · simp only [parentEnv, complexEnv, assignment, hi, dite_false, hbi, ite_true, hsi, realEnv_odd]

theorem assignment_holds {count free : ℕ} (base frame inputs : ℕ) (y : Fin free → ℝ)
    (parent : Fin count → ℝ) (env : ℕ → ℂ) (prior : List Gate) (hb : free + inputs ≤ base)
    (hg : ∀ g ∈ prior, g.Holds env) (hr : ∀ i < frame, (env i).im = 0)
    (hp : ∀ i : Fin count, (env i.val).re = parent i) :
    (formula count frame free inputs base prior).Holds (assignment base y parent env) := by
  have hf : free ≤ base := by omega
  have hpoint : point count base (assignment base y parent env) = parent := by
    funext i
    have he := congrFun (assignment_parentEnv base y parent env hf) i.val
    exact (congrArg Complex.re he).trans (hp i)
  apply (holds_iff _ _ _ _ _ _ _).mpr
  rw [assignment_parentEnv base y parent env hf, hpoint]
  exact ⟨hg, hr, assignment_frozen base inputs y parent env hb⟩

end LeanCanny.ETR.ComplexCircuit.FrozenParentConstraint
