/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTime
public import LeanCanny.Encoding.Pairing
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Native certificates for polynomial-time string functions

The string, unary-number, and predicate interfaces are specializations of the
native tidy machine calculus. There is no intermediate machine model or compiler.
-/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

/-- Polynomial-time string functions, measured in the raw input length. -/
def FP : Set (List Bool → List Bool) :=
  {f | ComputableTidilyInPolyTime f encBits encBits}

theorem FP.computable {f : List Bool → List Bool} (hf : f ∈ FP) :
    ComputableTidilyInPolyTime f encBits encBits := hf

theorem flag_computable {f : List Bool → Bool} (hf : (fun z => [f z]) ∈ FP) :
    ComputableTidilyInPolyTime f encBits encBool := hf.of_enc_eq fun _ => rfl

/-- A natural-valued computation whose result can be written in unary. -/
abbrev UnaryFn (f : List Bool → ℕ) : Prop :=
  ComputableTidilyInPolyTime f encBits encUnary

/-- A predicate with a polynomial-time one-bit verdict. -/
def FPPred (p : List Bool → Prop) : Prop :=
  ∃ g : List Bool → Bool, (fun z => [g z]) ∈ FP ∧ ∀ z, p z ↔ g z = true

theorem id_mem_FP : id ∈ FP := ComputableTidilyInPolyTime.id'

theorem constFn_mem_FP (w : List Bool) : (fun _ => w) ∈ FP :=
  ComputableTidilyInPolyTime.const w

theorem mem_FP_comp {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (g ∘ f) ∈ FP := hg.comp hf

theorem mem_FP_of_eq {f g : List Bool → List Bool} (hf : f ∈ FP) (h : ∀ z, f z = g z) :
    g ∈ FP := by
  simpa only [funext h] using hf

theorem reverse_mem_FP : List.reverse ∈ FP := ComputableTidilyInPolyTime.bitsReverse

theorem cons_mem_FP (bit : Bool) : List.cons bit ∈ FP := by
  exact (ComputableTidilyInPolyTime.const (encIn := encBits) (encMid := encBits) [bit]).append
    ComputableTidilyInPolyTime.id' fun _ => rfl

theorem appendFn_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun z => a z ++ b z) ∈ FP := ha.append hb fun _ => rfl

theorem output_length_poly_of_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) :
    ∃ p : Polynomial ℕ, ∀ z, (f z).length ≤ p.eval z.length := by
  obtain ⟨c, d, h⟩ := hf.polyBounded_length.exists_le
  exact ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun z => by
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, encBits_apply] using h z⟩

theorem UnaryFn.mem_FP {f : List Bool → ℕ} (hf : UnaryFn f) :
    (fun z => List.replicate (f z) true) ∈ FP := hf.encoded

theorem unaryFn_iff {f : List Bool → ℕ} :
    UnaryFn f ↔ (fun z => List.replicate (f z) true) ∈ FP :=
  ⟨UnaryFn.mem_FP, fun hf => hf.of_enc_eq fun _ => rfl⟩

theorem UnaryFn.of_eq {f g : List Bool → ℕ} (hf : UnaryFn f)
    (h : ∀ z, f z = g z) : UnaryFn g := by
  simpa only [funext h] using hf

theorem UnaryFn.comp {f : List Bool → ℕ} {g : List Bool → List Bool}
    (hf : UnaryFn f) (hg : g ∈ FP) : UnaryFn (fun z => f (g z)) :=
  ComputableTidilyInPolyTime.comp hf hg

theorem UnaryFn.length {f : List Bool → List Bool} (hf : f ∈ FP) :
    UnaryFn (fun z => (f z).length) :=
  ComputableTidilyInPolyTime.length_bits.comp hf

theorem UnaryFn.const (n : ℕ) : UnaryFn (fun _ => n) :=
  ComputableTidilyInPolyTime.const n

theorem UnaryFn.replicate_mem_FP {f : List Bool → ℕ} (hf : UnaryFn f) (bit : Bool) :
    (fun z => List.replicate (f z) bit) ∈ FP := by
  have h := ComputableTidilyInPolyTime.foldl_of_bounded_growth
    (encA := encBool) (encL := encBits) (list := fun z => List.replicate (f z) true)
    (init := fun _ => []) (step := fun acc _ => bit :: acc) hf.encoded
    (ComputableTidilyInPolyTime.const [])
    (show ComputableTidilyInPolyTime (fun p : List Bool × Bool => bit :: p.1)
      (encPair encBits encBool) encBits from
      (cons_mem_FP bit).comp (ComputableTidilyInPolyTime.fst encBits encBool))
    (growth := 1) (fun _ _ => by simp)
  have heq (n : ℕ) : (List.cons bit)^[n] [] = List.replicate n bit := by
    induction n with
    | zero => rfl
    | succ n ih => simp [Function.iterate_succ_apply', ih, List.replicate_succ]
  change ComputableTidilyInPolyTime _ encBits encBits
  simpa only [List.foldl_const, List.length_replicate, heq] using h

theorem UnaryFn.add {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => f z + g z) :=
  ComputableTidilyInPolyTime.unary_add.comp (hf.prod hg)

theorem UnaryFn.sub {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => f z - g z) :=
  ComputableTidilyInPolyTime.unary_sub.comp (hf.prod hg)

theorem UnaryFn.mul {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => f z * g z) :=
  ComputableTidilyInPolyTime.unary_mul.comp (hf.prod hg)

theorem UnaryFn.min {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => min (f z) (g z)) :=
  ComputableTidilyInPolyTime.unary_min.comp (hf.prod hg)

theorem UnaryFn.max {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => max (f z) (g z)) :=
  (hf.add (hg.sub hf)).of_eq fun _ => by omega

theorem UnaryFn.pow_const {f : List Bool → ℕ} (hf : UnaryFn f) (n : ℕ) :
    UnaryFn (fun z => f z ^ n) := (ComputableTidilyInPolyTime.unary_pow n).comp hf

theorem FPPred.of_flag {g : List Bool → Bool} (hg : (fun z => [g z]) ∈ FP) :
    FPPred (fun z => g z = true) := ⟨g, hg, fun _ => Iff.rfl⟩

theorem FPPred.of_computable {p : List Bool → Prop} {g : List Bool → Bool}
    (hg : ComputableTidilyInPolyTime g encBits encBool) (h : ∀ z, p z ↔ g z = true) :
    FPPred p := ⟨g, hg.encoded, h⟩

theorem FPPred.computable {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) :
    ComputableTidilyInPolyTime (fun z => decide (p z)) encBits encBool := by
  obtain ⟨g, hg, h⟩ := hp
  refine hg.of_enc_eq fun z => ?_
  change [decide (p z)] = [g z]
  by_cases hp : p z
  · rw [decide_eq_true hp, (h z).mp hp]
  · rw [decide_eq_false hp, Bool.eq_false_iff.mpr fun hv => hp ((h z).mpr hv)]

theorem FPPred.flag_mem_FP {p : List Bool → Prop} [DecidablePred p] (hp : FPPred p) :
    (fun z => [decide (p z)]) ∈ FP := hp.computable.encoded

theorem FPPred.of_iff {p q : List Bool → Prop} (hp : FPPred p)
    (h : ∀ z, p z ↔ q z) : FPPred q := by
  obtain ⟨g, hg, hp⟩ := hp
  exact ⟨g, hg, fun z => (h z).symm.trans (hp z)⟩

theorem FPPred.comp {p : List Bool → Prop} {g : List Bool → List Bool}
    (hp : FPPred p) (hg : g ∈ FP) : FPPred (fun z => p (g z)) := by
  obtain ⟨f, hf, hp⟩ := hp
  exact ⟨fun z => f (g z), mem_FP_comp hg hf, fun z => hp (g z)⟩

theorem FPPred.const (p : Prop) [Decidable p] : FPPred (fun _ => p) :=
  ⟨fun _ => decide p, constFn_mem_FP _, fun _ => decide_eq_true_iff.symm⟩

theorem FPPred.le {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    FPPred (fun z => f z ≤ g z) :=
  .of_computable (ComputableTidilyInPolyTime.unary_le.comp (hf.prod hg))
    fun _ => decide_eq_true_iff.symm

theorem FPPred.lt {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    FPPred (fun z => f z < g z) :=
  .of_computable (ComputableTidilyInPolyTime.unary_lt.comp (hf.prod hg))
    fun _ => decide_eq_true_iff.symm

theorem FPPred.eq {f g : List Bool → ℕ} (hf : UnaryFn f) (hg : UnaryFn g) :
    FPPred (fun z => f z = g z) :=
  .of_computable (ComputableTidilyInPolyTime.decide_eq encUnary |>.comp (hf.prod hg))
    fun _ => decide_eq_true_iff.symm

theorem FPPred.and {p q : List Bool → Prop} (hp : FPPred p) (hq : FPPred q) :
    FPPred (fun z => p z ∧ q z) := by
  classical
  exact .of_computable (hp.computable.decide_and hq.computable)
    fun _ => decide_eq_true_iff.symm

theorem FPPred.or {p q : List Bool → Prop} (hp : FPPred p) (hq : FPPred q) :
    FPPred (fun z => p z ∨ q z) := by
  classical
  exact .of_computable (hp.computable.decide_or hq.computable)
    fun _ => decide_eq_true_iff.symm

theorem FPPred.not {p : List Bool → Prop} (hp : FPPred p) :
    FPPred (fun z => ¬p z) := by
  obtain ⟨g, hg, h⟩ := hp
  have hgBool : ComputableTidilyInPolyTime g encBits encBool :=
    hg.of_enc_eq fun _ => rfl
  refine .of_computable (ComputableTidilyInPolyTime.bool_not.comp hgBool) fun z => ?_
  simp only [h z, Function.comp_apply, Bool.not_eq_true', Bool.eq_false_iff]

theorem FPPred.ite_mem_FP {p : List Bool → Prop} [DecidablePred p]
    {f g : List Bool → List Bool} (hp : FPPred p) (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => if p z then f z else g z) ∈ FP := hp.computable.ite_decide hf hg

theorem UnaryFn.ite {p : List Bool → Prop} [DecidablePred p] {f g : List Bool → ℕ}
    (hp : FPPred p) (hf : UnaryFn f) (hg : UnaryFn g) :
    UnaryFn (fun z => if p z then f z else g z) := hp.computable.ite_decide hf hg

theorem take_mem_FP {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) : (fun z => (f z).take (n z)) ∈ FP :=
  ComputableTidilyInPolyTime.bitsTakeWithInput hf hn

theorem drop_mem_FP {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) : (fun z => (f z).drop (n z)) ∈ FP :=
  ComputableTidilyInPolyTime.bitsDropWithInput hf hn

theorem getBit_mem_FP {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) :
    (fun z => [(f z)[n z]?.getD false]) ∈ FP := by
  exact (ComputableTidilyInPolyTime.bitsGetDWithInput hf hn false).of_enc_eq
    fun _ => by simp only [encBits_apply, encBool, List.getD_eq_getElem?_getD]; rfl

theorem FPPred.getBit {f : List Bool → List Bool} {n : List Bool → ℕ}
    (hf : f ∈ FP) (hn : UnaryFn n) : FPPred (fun z => (f z)[n z]?.getD false = true) :=
  .of_flag (getBit_mem_FP hf hn)

end LeanCanny
