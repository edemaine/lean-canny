/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexPowerSize
public import LeanCanny.Computation.PolyTimeIteration

/-! # Native polynomial-time generation of binary-power networks

A right fold appends two shared multiplication gates per exponent bit. The
fresh-wire counter and the complete encoded forest have polynomial bounds
in the literal exponent length and the supplied unary wire indices.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Power
open LeanCanny.Encoding.Brackets Turing.MultiTapeTM

namespace Encoded

def code (s : ℕ × List Bool) : List Bool := pair (List.replicate s.1 true) s.2
def parameter (bits : List Bool) : List Bool := pairFst (pairFst bits)
def work (bits : List Bool) : List Bool := pairSnd (pairFst bits)
def baseIndex (bits : List Bool) : ℕ := (pairFst (parameter bits)).length
def startIndex (bits : List Bool) : ℕ := (pairSnd (parameter bits)).length
def currentIndex (bits : List Bool) : ℕ := (pairFst (work bits)).length
def chosenIndex (bits : List Bool) : ℕ := if pairSnd bits = [true] then baseIndex bits else startIndex bits

theorem parameter_mem_FP : parameter ∈ FP := mem_FP_comp (f := pairFst) (g := pairFst) pairFst_mem_FP pairFst_mem_FP
theorem work_mem_FP : work ∈ FP := mem_FP_comp (f := pairFst) (g := pairSnd) pairFst_mem_FP pairSnd_mem_FP

attribute [local irreducible] parameter work pairFst pairSnd

theorem baseIndex_unary : UnaryFn baseIndex :=
  (UnaryFn.length (mem_FP_comp (f := parameter) (g := pairFst) parameter_mem_FP pairFst_mem_FP)).of_eq (fun _ => rfl)

theorem startIndex_unary : UnaryFn startIndex :=
  (UnaryFn.length (mem_FP_comp (f := parameter) (g := pairSnd) parameter_mem_FP pairSnd_mem_FP)).of_eq (fun _ => rfl)

theorem currentIndex_unary : UnaryFn currentIndex :=
  (UnaryFn.length (mem_FP_comp (f := work) (g := pairFst) work_mem_FP pairFst_mem_FP)).of_eq (fun _ => rfl)

theorem chosenIndex_unary : UnaryFn chosenIndex := by
  have h := UnaryFn.ite (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true])) baseIndex_unary startIndex_unary
  exact h.of_eq (fun _ => rfl)

attribute [local irreducible] baseIndex startIndex currentIndex chosenIndex

def step (bits : List Bool) : List Bool :=
  pair (List.replicate (currentIndex bits + 2) true)
    (pairSnd (work bits) ++ arithmeticGateBits 2 (currentIndex bits + 1) (currentIndex bits) (currentIndex bits) ++
      arithmeticGateBits 2 (currentIndex bits + 2) (currentIndex bits + 1) (chosenIndex bits))

theorem step_mem_FP : step ∈ FP := by
  have ha := mem_FP_comp (f := work) (g := pairSnd) work_mem_FP pairSnd_mem_FP
  have hc := (currentIndex_unary.add (UnaryFn.const 2)).replicate_mem_FP true
  have hg1 := arithmeticGateBits_mem_FP 2 (currentIndex_unary.add (UnaryFn.const 1)) currentIndex_unary currentIndex_unary
  have hg2 := arithmeticGateBits_mem_FP 2 (currentIndex_unary.add (UnaryFn.const 2))
    (currentIndex_unary.add (UnaryFn.const 1)) chosenIndex_unary
  have h := mem_FP_pair hc (appendFn_mem_FP (appendFn_mem_FP ha hg1) hg2)
  apply mem_FP_of_eq h
  intro bits
  rfl

def next (par : ℕ × ℕ) (state : List Bool) (bit : Bool) : List Bool :=
  step (pair (pair (pair (List.replicate par.1 true) (List.replicate par.2 true)) state) [bit])

theorem next_code (base start counter : ℕ) (acc : List Bool) (bit : Bool) :
    next (base, start) (code (counter, acc)) bit = code (counter + 2,
      acc ++ arithmeticGateBits 2 (counter + 1) counter counter ++
        arithmeticGateBits 2 (counter + 2) (counter + 1) (if bit then base else start)) := by
  cases bit <;> simp [next, step, code, parameter, work, baseIndex, startIndex, currentIndex, chosenIndex]

theorem next_computable : ComputableTidilyInPolyTime
    (fun p : ((ℕ × ℕ) × List Bool) × Bool => next p.1.1 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encUnary) encBits) encBool) encBits := by
  have htuple := ComputableTidilyInPolyTime.fst (encPair (encPair encUnary encUnary) encBits) encBool
  have hp := htuple.fst'
  have hb := hp.fst'
  have hs := hp.snd'
  have hw := htuple.snd'
  have ht := ComputableTidilyInPolyTime.snd (encPair (encPair encUnary encUnary) encBits) encBool
  have hpacket := pair_computable (pair_computable (pair_computable hb.encoded hs.encoded) hw) ht.encoded
  have h := (FP.computable step_mem_FP).comp hpacket
  exact h.of_enc_eq (fun _ => rfl)

end Encoded

theorem stateBudget_unary {base start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hb : UnaryFn base) (hs : UnaryFn start) (he : bits ∈ FP) :
    UnaryFn (fun c => stateBudget (base c) (start c) (bits c).length) := by
  have hk := UnaryFn.length he
  have hstep := (((UnaryFn.const 10).mul (hs.add ((UnaryFn.const 2).mul hk))).add
    ((UnaryFn.const 2).mul (hb.add hs))).add (UnaryFn.const 44)
  have hforest := (((UnaryFn.const 2).mul hs).add (UnaryFn.const 22)).add (hk.mul hstep)
  have hstate := ((((UnaryFn.const 2).mul (hs.add ((UnaryFn.const 2).mul hk))).add (UnaryFn.const 2))).add hforest
  exact hstate.of_eq (fun _ => rfl)

theorem encode_mem_FP {base start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hb : UnaryFn base) (hs : UnaryFn start) (he : bits ∈ FP) :
    (fun c => encode (gates (base c) (start c) (bits c))) ∈ FP := by
  let g := fun c tail => (output (start c) tail, forest (gates (base c) (start c) tail))
  have hconst : (fun c => (Gate.constant (start c) 1).encode) ∈ FP :=
    mem_FP_of_eq (constantGateBits_mem_FP hs (constFn_mem_FP (Term.const 1).toData.toBits))
      (fun c => constantGateBits_encode (start c) 1)
  have hi := pair_computable hs.encoded hconst
  have hinit : ComputableTidilyInPolyTime (fun c => Encoded.code (g c [])) encBits encBits := by
    apply hi.of_enc_eq
    intro c
    simp only [Encoded.code, g, output, gates_nil, forest_cons, forest_nil, List.append_nil,
      List.length_nil, Nat.mul_zero, Nat.add_zero, encBits_apply, encUnary_apply]
  have hsize : PolyBounded (fun c : List Bool => (encBits c).length)
      (fun c => stateBudget (base c) (start c) (bits c).length) := by
    simpa only [encUnary_apply, List.length_replicate] using (stateBudget_unary hb hs he).polyBounded_length
  have hcode := foldrEncodedWith_spec Encoded.code (hb.prod hs) he hinit Encoded.next_computable
    (fun c tail bit => by
      dsimp only [g]
      rw [Encoded.next_code, output_cons, gates_cons, forest_append]
      simp only [forest_cons, forest_nil, List.append_nil, mulGateBits_encode, List.append_assoc])
    hsize (fun c tail ht => by
      have hlen := ht.length_le
      have hf := (forest_length_le (base c) (start c) tail).trans (forestBudget_mono (base c) (start c) hlen)
      simp only [Encoded.code, g, pair_length, List.length_replicate]
      dsimp only [stateBudget, output]
      omega)
  have ho := (FP.computable LeanCanny.Encoding.Brackets.wrap_mem_FP).comp
    ((FP.computable pairSnd_mem_FP).comp hcode)
  apply ho.of_enc_eq
  intro c
  simp only [Encoded.code, g, Function.comp_apply, pairSnd_pair, encBits_apply]
  exact encode_eq_wrap _

theorem forest_mem_FP {base start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hb : UnaryFn base) (hs : UnaryFn start) (he : bits ∈ FP) :
    (fun c => forest (gates (base c) (start c) (bits c))) ∈ FP := by
  have h := mem_FP_comp (encode_mem_FP hb hs he) contents_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, encode, contents_toBits, forest, List.map_map, Function.comp_def]
  rfl

end LeanCanny.ETR.ComplexCircuit.Power
