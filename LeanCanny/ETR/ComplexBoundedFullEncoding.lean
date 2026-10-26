/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedFullSource
public import LeanCanny.ETR.ComplexSampledEncoding

/-! # Native encoding of the full variable-coordinate regular source -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedFullSource

theorem tailStart_unary {source : List Bool → List Bool} {start : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) : UnaryFn (fun c => tailStart (start c) (TermView.term (source c))) :=
  (hs.add (SampledSource.count_unary ht)).of_eq (fun _ => rfl)

theorem sourceOutput_unary {source : List Bool → List Bool} {parameter start : List Bool → ℕ}
    (ht : source ∈ FP) (hp : UnaryFn parameter) (hs : UnaryFn start) :
    UnaryFn (fun c => sourceOutput (TermView.term (source c)).toData.size (parameter c) (start c) (TermView.term (source c))) := by
  have ho := UnaryFn.comp (f := Source.Machine.outputIndex) (g := source) Source.Machine.outputIndex_unary ht
  exact (CircuitFreeze.output_unary (FrozenSource.source_start_unary ht) hp hs ho).of_eq
    (fun c => by simp only [Source.Machine.outputIndex_eq, sourceOutput])

theorem termProgram_encode_mem_FP {source : List Bool → List Bool} {parameter start : List Bool → ℕ}
    (ht : source ∈ FP) (hp : UnaryFn parameter) (hs : UnaryFn start) :
    (fun c => encode (StraightLine.gates (start c)
      (termProgram (TermView.term (source c)).toData.size (parameter c) (start c) (TermView.term (source c))))) ∈ FP :=
  CircuitFreeze.encode_mem_FP (FrozenSource.source_start_unary ht) hp hs
    (by simpa only [Source.gates_eq] using Source.encoded_gates_mem_FP ht)

theorem output_unary {source radius scale shift bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP)
    (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => output (start c) (m c) (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c) (exponent c)) :=
  BoundedTail.output_unary (tailStart_unary ht hs) hm hR hF hb hN hE

theorem energyOutput_unary {source radius : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) :
    UnaryFn (fun c => energyOutput (start c) (m c) (TermView.term (source c)) (radius c)) :=
  BoundedTail.energyOutput_unary (tailStart_unary ht hs) hm hR

theorem length_unary {source radius scale shift bits exponent : List Bool → List Bool} {parameter start m : List Bool → ℕ}
    (ht : source ∈ FP) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP)
    (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => (program (TermView.term (source c)).toData.size (parameter c) (start c) (m c)
      (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c) (exponent c)).length) := by
  have hl := BoundedTail.length_unary (source := fun c => sourceOutput (TermView.term (source c)).toData.size
    (parameter c) (start c) (TermView.term (source c))) (sample := parameter)
    (start := fun c => tailStart (start c) (TermView.term (source c))) hm hR hF hb hN hE
  exact ((SampledSource.count_unary ht).add hl).of_eq
    (fun _ => by rw [program, List.length_append, termProgram_length])

theorem encode_mem_FP {source radius scale shift bits exponent : List Bool → List Bool} {parameter start m : List Bool → ℕ}
    (ht : source ∈ FP) (hp : UnaryFn parameter) (hs : UnaryFn start) (hm : UnaryFn m)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (TermView.term (source c)).toData.size (parameter c) (start c) (m c)
        (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c) (exponent c)))) ∈ FP := by
  unfold program
  apply StraightLine.encode_append_mem_FP (termProgram_encode_mem_FP ht hp hs)
  simp only [termProgram_next]
  exact BoundedTail.encode_mem_FP (sourceOutput_unary ht hp hs) hp (tailStart_unary ht hs) hm hR hF hb hN hE

end LeanCanny.ETR.ComplexCircuit.BoundedFullSource
