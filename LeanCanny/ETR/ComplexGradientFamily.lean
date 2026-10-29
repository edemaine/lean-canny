/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexHessianFamily

/-! # Shared gradient copies for a variable block

Each fresh initialized copy differentiates an entire shared program in one
coordinate of a selected input block. Source outputs and derivative outputs
remain available for all equations in a square system. Inputs before the
block may be constrained real while the block itself remains complex.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.GradientFamily
open MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical

abbrev stride := HessianFamily.stride
abbrev blockStart := HessianFamily.blockStart

def valueWire (base start : ℕ) (ops : List Operation) (q out : ℕ) : ℕ :=
  blockStart base start ops q + Differential.valueWire (Differential.valueWire out)
def derivativeWire (base start : ℕ) (ops : List Operation) (q out : ℕ) : ℕ :=
  blockStart base start ops q + Differential.derivativeWire (Differential.valueWire out)

def program (zWire base start offset : ℕ) (ops : List Operation) : ℕ → List Operation
  | 0 => []
  | count + 1 => program zWire base start offset ops count ++
      Hessian.program zWire (blockStart base start ops count) start 0 (offset + count) ops

def gates (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ) : List Gate :=
  StraightLine.gates base (program zWire base start offset ops count)

theorem program_length (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ) :
    (program zWire base start offset ops count).length = count * stride start ops := by
  induction count with
  | zero => simp only [program, List.length_nil, Nat.zero_mul]
  | succ count ih =>
    simp only [program, List.length_append, Hessian.program_length, ih, stride, HessianFamily.stride, Nat.succ_mul]

theorem next_eq (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ) :
    base + (program zWire base start offset ops count).length = blockStart base start ops count := by
  rw [program_length]
  rfl

theorem gates_succ (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ) :
    gates zWire base start offset ops (count + 1) = gates zWire base start offset ops count ++
      StraightLine.gates (blockStart base start ops count)
        (Hessian.program zWire (blockStart base start ops count) start 0 (offset + count) ops) := by
  rw [gates, program, StraightLine.gates_append, next_eq]
  rfl

theorem gates_range (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ) :
    gates zWire base start offset ops count = (List.range count).flatMap (fun q =>
      StraightLine.gates (blockStart base start ops q)
        (Hessian.program zWire (blockStart base start ops q) start 0 (offset + q) ops)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [gates_succ, ih, List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem wellFormed (zWire base start offset : ℕ) (ops : List Operation) (count : ℕ)
    (hz : zWire < base) (hs : start ≤ base) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed base (program zWire base start offset ops count) := by
  induction count with
  | zero => trivial
  | succ count ih =>
    rw [program, StraightLine.wellFormed_append, next_eq]
    have hb : base ≤ blockStart base start ops count := by unfold blockStart HessianFamily.blockStart; omega
    exact ⟨ih, Hessian.wellFormed zWire _ start _ _ ops (hz.trans_le hb) (hs.trans hb) hw⟩

theorem sound (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start offset : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (x env : ℕ → ℂ) (hz : env zWire = 0)
    (hx : ∀ i < start, env i = x i) (count : ℕ)
    (hg : ∀ g ∈ gates zWire base start offset ops count, g.Holds env)
    (q : ℕ) (hq : q < count) (out : ℕ) (ho : out < start + ops.length) :
    env (valueWire base start ops q out) = (wire out).eval₂ (Int.castRingHom ℂ) x ∧
      env (derivativeWire base start ops q out) = (pderiv (offset + q) (wire out)).eval₂ (Int.castRingHom ℂ) x := by
  have hcopy : ∀ g ∈ StraightLine.gates (blockStart base start ops q)
      (Hessian.program zWire (blockStart base start ops q) start 0 (offset + q) ops), g.Holds env := by
    intro g h
    exact hg g (by rw [gates_range]; exact List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, h⟩)
  have H := Hessian.sound wire zWire _ start 0 (offset + q) ops hw hr hin x env hz hx hcopy out ho
  exact ⟨H.1, H.2.1⟩

theorem exists_completion (wire : ℕ → MvPolynomial ℕ ℤ) (zWire base start offset : ℕ) (ops : List Operation)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (hz : zWire < base) (hs : start ≤ base)
    (x : ℕ → ℂ) (hx : x zWire = 0) (count : ℕ) :
    ∃ env : ℕ → ℂ, (∀ i < base, env i = x i) ∧
      (∀ g ∈ gates zWire base start offset ops count, g.Holds env) ∧
      ∀ q < count, ∀ out < start + ops.length,
        env (valueWire base start ops q out) = (wire out).eval₂ (Int.castRingHom ℂ) x ∧
          env (derivativeWire base start ops q out) = (pderiv (offset + q) (wire out)).eval₂ (Int.castRingHom ℂ) x := by
  obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x base (program zWire base start offset ops count)
    (wellFormed zWire base start offset ops count hz hs hw)
  exact ⟨env, hp, hg, fun q hq out ho => sound wire zWire base start offset ops hw hr hin x env
    ((hp _ hz).trans hx) (fun i hi => hp i (hi.trans_le hs)) count hg q hq out ho⟩

theorem derivativeWire_lt_end (base start : ℕ) (ops : List Operation) (count q out : ℕ)
    (hq : q < count) (ho : out < start + ops.length) :
    derivativeWire base start ops q out < base + count * stride start ops := by
  have hi : Differential.derivativeWire (Differential.valueWire out) < stride start ops := by
    dsimp [Differential.derivativeWire, Differential.valueWire, stride, HessianFamily.stride]
    omega
  calc
    _ < blockStart base start ops q + stride start ops := Nat.add_lt_add_left hi _
    _ = base + (q + 1) * stride start ops := by unfold blockStart HessianFamily.blockStart; ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ hq) _

theorem valueWire_lt_end (base start : ℕ) (ops : List Operation) (count q out : ℕ)
    (hq : q < count) (ho : out < start + ops.length) :
    valueWire base start ops q out < base + count * stride start ops := by
  have H := derivativeWire_lt_end base start ops count q out hq ho
  dsimp [valueWire, derivativeWire, Differential.derivativeWire, Differential.valueWire] at *
  omega

theorem valueWire_unary {base start q out : List Bool → ℕ} {ops : List Bool → List Operation}
    (hb : UnaryFn base) (hs : UnaryFn start) (hq : UnaryFn q) (ho : UnaryFn out)
    (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => valueWire (base c) (start c) (ops c) (q c) (out c)) :=
  ((hb.add (hq.mul ((UnaryFn.const 16).mul (hs.add hlen)))).add
    ((UnaryFn.const 16).mul ho)).of_eq (fun _ => by
      dsimp [valueWire, blockStart, HessianFamily.blockStart, stride, HessianFamily.stride, Differential.valueWire]
      omega)

theorem derivativeWire_unary {base start q out : List Bool → ℕ} {ops : List Bool → List Operation}
    (hb : UnaryFn base) (hs : UnaryFn start) (hq : UnaryFn q) (ho : UnaryFn out)
    (hlen : UnaryFn (fun c => (ops c).length)) :
    UnaryFn (fun c => derivativeWire (base c) (start c) (ops c) (q c) (out c)) :=
  ((valueWire_unary hb hs hq ho hlen).add (UnaryFn.const 3)).of_eq (fun _ => rfl)

theorem encode_mem_FP {zWire base start offset count : List Bool → ℕ} {ops : List Bool → List Operation}
    (hz : UnaryFn zWire) (hb : UnaryFn base) (hs : UnaryFn start) (hoff : UnaryFn offset) (hc : UnaryFn count)
    (hlen : UnaryFn (fun c => (ops c).length))
    (hg : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (gates (zWire c) (base c) (start c) (offset c) (ops c) (count c))) ∈ FP := by
  have hz' := hz.comp pairFst_mem_FP
  have hb' := hb.comp pairFst_mem_FP
  have hs' := hs.comp pairFst_mem_FP
  have hoff' := hoff.comp pairFst_mem_FP
  have hl' := hlen.comp pairFst_mem_FP
  have hq := UnaryFn.length pairSnd_mem_FP
  have hblock := hb'.add (hq.mul ((UnaryFn.const 16).mul (hs'.add hl')))
  have hcopy := Hessian.program_encode_mem_FP hz' hblock hs' (UnaryFn.const 0) (hoff'.add hq)
    (mem_FP_comp pairFst_mem_FP hg)
  have h := mem_FP_comp (flatMap_range_mem_FP (mem_FP_comp hcopy contents_mem_FP) hc.mem_FP) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairFst_pair, pairSnd_pair, contents_encode]
  rw [encode_eq_wrap, gates_range]
  congr 1
  induction count c with
  | zero => rfl
  | succ k ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, forest_append, ih]
    rfl

end LeanCanny.ETR.ComplexCircuit.GradientFamily
