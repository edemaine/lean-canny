/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSampledSource

/-! # Native polynomial-time encoding of the complete sampled source

The generator retains both binary exponent words and all source/record reader
costs. Its actual operation count and output index have unary certificates,
so the resulting source can feed the shared critical-kernel query writer.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SampledSource
open LeanCanny.Encoding.Brackets

theorem count_unary {source : List Bool → List Bool} (ht : source ∈ FP) :
    UnaryFn (fun c => Source.count (TermView.term (source c))) := by
  have hn := UnaryFn.comp (f := Source.Machine.nextIndex) (g := source) Source.Machine.nextIndex_unary ht
  exact (hn.sub (FrozenSource.source_start_unary ht)).of_eq
    (fun c => by simp only [Source.Machine.nextIndex_eq, Nat.add_sub_cancel_left])

theorem powerStart_unary {source : List Bool → List Bool} {start : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) :
    UnaryFn (fun c => powerStart (start c) (TermView.term (source c))) :=
  ((hs.add (count_unary ht)).add (UnaryFn.const 1)).of_eq (fun _ => rfl)

theorem joinStart_unary {source bits : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (he : bits ∈ FP) :
    UnaryFn (fun c => joinStart (start c) (m c) (TermView.term (source c)) (bits c)) :=
  (((powerStart_unary ht hs).add (UnaryFn.const 1)).add ((hm.add (UnaryFn.const 1)).mul
    (((UnaryFn.const 2).mul (UnaryFn.length he)).add (UnaryFn.const 6)))).of_eq (fun _ => rfl)

theorem output_unary {source bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (he : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => output (start c) (m c) (TermView.term (source c)) (bits c) (exponent c)) :=
  ((Dyadic.productWire_unary ((joinStart_unary ht hs hm he).add (UnaryFn.const 3)) hE).add (UnaryFn.const 2)).of_eq
    (fun _ => rfl)

theorem length_unary {source bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    {sample a : List Bool → ℤ} (ht : source ∈ FP) (hm : UnaryFn m) (he : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => (program (TermView.term (source c)).toData.size (start c) (m c) (sample c) (a c)
      (TermView.term (source c)) (bits c) (exponent c)).length) :=
  ((((count_unary ht).add ((hm.add (UnaryFn.const 1)).mul
    (((UnaryFn.const 2).mul (UnaryFn.length he)).add (UnaryFn.const 6)))).add
      ((UnaryFn.const 2).mul (UnaryFn.length hE))).add (UnaryFn.const 10)).of_eq
        (fun _ => (program_length _ _ _ _ _ _ _ _).symm)

theorem encode_mem_FP {source bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    {sample a : List Bool → ℤ} (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (ha : (fun c => (Term.const (a c)).toData.toBits) ∈ FP) (he : bits ∈ FP) (hE : exponent ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (TermView.term (source c)).toData.size (start c) (m c) (sample c) (a c)
        (TermView.term (source c)) (bits c) (exponent c)))) ∈ FP := by
  have hpstart := powerStart_unary ht hs
  have hj := joinStart_unary ht hs hm he
  have hp := SamplePowers.output_unary hm hs hpstart he
  have hlow := FrozenSource.encode_mem_FP ht hs hsample
  have hpower := SamplePowers.encode_mem_FP hm hs hpstart he
  have hconstant := constantGateBits_mem_FP hj ha
  have hmul := arithmeticGateBits_mem_FP 2 (hj.add (UnaryFn.const 1)) hj hp
  have hadd := arithmeticGateBits_mem_FP 1 (hj.add (UnaryFn.const 2))
    (FrozenSource.output_unary ht hs) (hj.add (UnaryFn.const 1))
  have hdyadic := Dyadic.encode_mem_FP (hj.add (UnaryFn.const 2)) (hj.add (UnaryFn.const 3)) hE
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp hlow contents_mem_FP)
    (appendFn_mem_FP (mem_FP_comp hpower contents_mem_FP)
      (appendFn_mem_FP hconstant (appendFn_mem_FP hmul (appendFn_mem_FP hadd
        (mem_FP_comp hdyadic contents_mem_FP)))))) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode, mulGateBits_encode, addGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest_append, forest_cons, forest_nil, List.append_nil, List.append_assoc]
  rfl

end LeanCanny.ETR.ComplexCircuit.SampledSource
