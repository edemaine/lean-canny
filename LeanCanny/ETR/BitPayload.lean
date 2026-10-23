/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.BinaryDigits

/-!
# Polynomial-time decoding of binary payload forests

The serialized bit nodes are `01` and `0011`. Reading from right to left needs
four finite phases and an absorbing failure state. A successful run produces
exactly the list of bits whose node serializations formed the input. The output
list stays linearly bounded; no binary magnitude is expanded into unary.
-/

@[expose] public section

namespace LeanCanny.ETR.Codec.BitPayload

open LeanCanny.Encoding.Brackets

inductive Phase where
  | ready | oneClose | twoClose | needOpen | bad
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  output : List Bool
  deriving DecidableEq, Repr

def advance (b : Bool) (s : State) : State :=
  match s.phase, b with
  | .ready, true => ⟨.oneClose, s.output⟩
  | .oneClose, false => ⟨.ready, false :: s.output⟩
  | .oneClose, true => ⟨.twoClose, s.output⟩
  | .twoClose, false => ⟨.needOpen, s.output⟩
  | .needOpen, false => ⟨.ready, true :: s.output⟩
  | _, _ => ⟨.bad, []⟩

def run (bits : List Bool) : State := bits.foldr advance ⟨.ready, []⟩

@[simp] theorem run_nil : run [] = ⟨.ready, []⟩ := rfl

@[simp] theorem run_cons (b : Bool) (bits : List Bool) :
    run (b :: bits) = advance b (run bits) := rfl

theorem run_append (xs ys : List Bool) : run (xs ++ ys) = xs.foldr advance (run ys) := by
  exact List.foldr_append

def body (digits : List Bool) : List Bool := (digits.map (fun b => (Codec.bit b).toBits)).flatten

@[simp] theorem body_nil : body [] = [] := rfl

@[simp] theorem body_cons (b : Bool) (digits : List Bool) :
    body (b :: digits) = (Codec.bit b).toBits ++ body digits := rfl

theorem run_body (digits : List Bool) : run (body digits) = ⟨.ready, digits⟩ := by
  induction digits with
  | nil => rfl
  | cons b digits ih =>
      rw [body_cons, run_append, ih]
      cases b <;> simp [Codec.bit, Data.toBits_l, advance]

def pending : Phase → List Bool
  | .ready | .bad => []
  | .oneClose => [true]
  | .twoClose => [true, true]
  | .needOpen => [false, true, true]

/-- A nonfailure state describes an exact unmatched prefix followed by decoded bit nodes. -/
def PartialBody (bits : List Bool) (s : State) : Prop :=
  match s.phase with
  | .bad => True
  | _ => bits = pending s.phase ++ body s.output

theorem run_spec (bits : List Bool) : PartialBody bits (run bits) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
      cases hs : run bits with
      | mk phase output =>
          have hi : PartialBody bits ⟨phase, output⟩ := by simpa only [hs] using ih
          rw [run_cons, hs]
          cases phase <;> cases b <;>
            simp only [PartialBody, advance, pending] at hi ⊢
          all_goals rw [hi]; simp [Codec.bit, Data.toBits_l]

theorem body_of_ready (bits : List Bool) (h : (run bits).phase = .ready) :
    bits = body (run bits).output := by
  have hs := run_spec bits
  cases hr : run bits with
  | mk phase output =>
      cases phase <;> simp_all [PartialBody, pending]

theorem ready_iff (bits : List Bool) :
    (run bits).phase = .ready ↔ ∃ digits : List Bool, bits = body digits := by
  constructor
  · intro h
    exact ⟨(run bits).output, body_of_ready bits h⟩
  · rintro ⟨digits, rfl⟩
    rw [run_body]

theorem advance_output_length_le (b : Bool) (s : State) :
    (advance b s).output.length ≤ s.output.length + 1 := by
  cases s with
  | mk phase output => cases phase <;> cases b <;> simp [advance]

theorem run_output_length_le (bits : List Bool) : (run bits).output.length ≤ bits.length := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
      exact (advance_output_length_le b (run bits)).trans (by simpa using Nat.add_le_add_right ih 1)

/-- Fixed-width headers for the finite control of the decoder. -/
def header : Phase → List Bool
  | .ready => [false, false, false]
  | .oneClose => [false, false, true]
  | .twoClose => [false, true, false]
  | .needOpen => [false, true, true]
  | .bad => [true, false, false]

@[simp] theorem header_length (phase : Phase) : (header phase).length = 3 := by cases phase <;> rfl

def encode (s : State) : List Bool := header s.phase ++ s.output

@[simp] theorem encode_length (s : State) : (encode s).length = 3 + s.output.length := by
  simp [encode]

@[simp] theorem take_encode (s : State) : (encode s).take 3 = header s.phase := by
  rw [← header_length s.phase, encode, List.take_left]

@[simp] theorem drop_encode (s : State) : (encode s).drop 3 = s.output := by
  rw [← header_length s.phase, encode, List.drop_left]

/-- The string-level implementation is total, rejecting malformed finite-control headers. -/
def encodedAdvance (b : Bool) (xs : List Bool) : List Bool :=
  if xs.take 3 = header .ready then encode (advance b ⟨.ready, xs.drop 3⟩)
  else if xs.take 3 = header .oneClose then encode (advance b ⟨.oneClose, xs.drop 3⟩)
  else if xs.take 3 = header .twoClose then encode (advance b ⟨.twoClose, xs.drop 3⟩)
  else if xs.take 3 = header .needOpen then encode (advance b ⟨.needOpen, xs.drop 3⟩)
  else encode ⟨.bad, []⟩

theorem encodedAdvance_encode (b : Bool) (s : State) :
    encodedAdvance b (encode s) = encode (advance b s) := by
  cases s with
  | mk phase output => cases phase <;> cases b <;> simp [encodedAdvance, header, advance, encode]

theorem encodedAdvance_mem_FP (b : Bool) : encodedAdvance b ∈ FP := by
  have hdrop := drop_mem_FP id_mem_FP (UnaryFn.const 3)
  have hwrite (p : Phase) {f : List Bool → List Bool} (hf : f ∈ FP) :
      (fun z => header p ++ f z) ∈ FP := appendFn_mem_FP (constFn_mem_FP (header p)) hf
  have hbranch (p : Phase) : (fun xs => encode (advance b ⟨p, xs.drop 3⟩)) ∈ FP := by
    cases p <;> cases b <;> simp only [advance, encode]
    all_goals first
      | exact constFn_mem_FP _
      | exact hwrite _ hdrop
      | exact hwrite _ (mem_FP_comp hdrop (cons_mem_FP false))
      | exact hwrite _ (mem_FP_comp hdrop (cons_mem_FP true))
  have htest (p : Phase) : FPPred (fun xs : List Bool => xs.take 3 = header p) :=
    stringEq_fppred (take_mem_FP id_mem_FP (UnaryFn.const 3)) (constFn_mem_FP (header p))
  exact (htest .ready).ite_mem_FP (hbranch .ready)
    ((htest .oneClose).ite_mem_FP (hbranch .oneClose)
      ((htest .twoClose).ite_mem_FP (hbranch .twoClose)
        ((htest .needOpen).ite_mem_FP (hbranch .needOpen) (constFn_mem_FP _))))

/-- The complete decoder runs in the machine-level polynomial-time class. -/
theorem runEncoded_mem_FP : (fun bits => encode (run bits)) ∈ FP := by
  let step := fun (_ : List Bool) acc bit => encodedAdvance bit acc
  have hacc : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => p.1.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by fun_prop
  have hstep : Turing.MultiTapeTM.ComputableTidilyInPolyTime
      (fun p : (List Bool × List Bool) × Bool => step p.1.1 p.1.2 p.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
        Turing.MultiTapeTM.encBool) Turing.MultiTapeTM.encBits := by
    have hb := Turing.MultiTapeTM.ComputableTidilyInPolyTime.snd
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool
    exact (hb.cond ((encodedAdvance_mem_FP true).comp hacc)
      ((encodedAdvance_mem_FP false).comp hacc)).of_enc_eq
        fun p => by cases p.2 <;> rfl
  refine foldrEncodedWith_spec encode (step := step) (g := fun _ bits => run bits)
    (constFn_mem_FP []) id_mem_FP (constFn_mem_FP (encode ⟨.ready, []⟩)) hstep
    (fun _ bits bit => encodedAdvance_encode bit (run bits))
    (((PolyBound.const 3).add PolyBound.id).polyBounded (fun z : List Bool => z.length)) ?_
  intro z bits hbits
  rw [encode_length]
  exact Nat.add_le_add_left ((run_output_length_le bits).trans hbits.length_le) 3

theorem output_mem_FP : (fun bits => (run bits).output) ∈ FP := by
  refine mem_FP_of_eq (drop_mem_FP runEncoded_mem_FP (UnaryFn.const 3)) fun bits => ?_
  exact drop_encode _

theorem ready_fppred : FPPred (fun bits => (run bits).phase = .ready) := by
  have hh := stringEq_fppred (take_mem_FP runEncoded_mem_FP (UnaryFn.const 3))
    (constFn_mem_FP (header .ready))
  refine hh.of_iff fun bits => ?_
  rw [take_encode]
  cases (run bits).phase <;> decide

end LeanCanny.ETR.Codec.BitPayload
