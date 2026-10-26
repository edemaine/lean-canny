/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedSource
public import LeanCanny.ETR.ComplexSampledEncoding

/-! # Native polynomial-time encoding of the bounded regular source

The bounds depend on the original source reader, unary spatial dimension,
the sample literal and five binary exponent words. No expanded coefficient
or expanded power of the original term is required.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedSource
open LeanCanny.Encoding.Brackets

theorem radialStart_unary {source : List Bool → List Bool} {start : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) : UnaryFn (fun c => radialStart (start c) (TermView.term (source c))) :=
  SampledSource.powerStart_unary ht hs

theorem lowStart_unary {source : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) :
    UnaryFn (fun c => lowStart (start c) (m c) (TermView.term (source c))) :=
  SampledSource.joinStart_unary ht hs hm (constFn_mem_FP [true])

theorem powerStart_unary {source radius scale shift : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    UnaryFn (fun c => powerStart (start c) (m c) (TermView.term (source c)) (radius c) (scale c) (shift c)) :=
  ((BoundedLow.output_unary (lowStart_unary ht hs hm) hR hF hb).add (UnaryFn.const 1)).of_eq (fun _ => rfl)

theorem joinStart_unary {source radius scale shift bits : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP)
    (hb : shift ∈ FP) (hN : bits ∈ FP) :
    UnaryFn (fun c => joinStart (start c) (m c) (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c)) :=
  (((powerStart_unary ht hs hm hR hF hb).add (UnaryFn.const 1)).add
    ((hm.add (UnaryFn.const 3)).mul (((UnaryFn.const 2).mul (UnaryFn.length hN)).add (UnaryFn.const 6)))).of_eq (fun _ => rfl)

theorem output_unary {source radius scale shift bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP)
    (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => output (start c) (m c) (TermView.term (source c))
      (radius c) (scale c) (shift c) (bits c) (exponent c)) :=
  ((Dyadic.productWire_unary ((joinStart_unary ht hs hm hR hF hb hN).add (UnaryFn.const 1)) hE).add
    (UnaryFn.const 2)).of_eq (fun _ => rfl)

theorem length_unary {source radius scale shift bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    {sample : List Bool → ℤ} (ht : source ∈ FP) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP)
    (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => (program (TermView.term (source c)).toData.size (start c) (m c) (sample c)
      (TermView.term (source c)) (radius c) (scale c) (shift c) (bits c) (exponent c)).length) :=
  ((((((((SampledSource.count_unary ht).add ((UnaryFn.const 8).mul (hm.add (UnaryFn.const 1)))).add
    ((UnaryFn.const 2).mul (UnaryFn.length hR))).add ((UnaryFn.const 2).mul (UnaryFn.length hF))).add
      ((UnaryFn.const 2).mul (UnaryFn.length hb))).add ((hm.add (UnaryFn.const 3)).mul
        (((UnaryFn.const 2).mul (UnaryFn.length hN)).add (UnaryFn.const 6)))).add
          ((UnaryFn.const 2).mul (UnaryFn.length hE))).add (UnaryFn.const 25)).of_eq
            (fun _ => (program_length _ _ _ _ _ _ _ _ _ _).symm)

private theorem add_encode_mem_FP {start left right : List Bool → ℕ}
    (hs : UnaryFn start) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => encode (StraightLine.gates (start c) [.add (left c) (right c)])) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (arithmeticGateBits_mem_FP 1 hs hl hr) wrap_mem_FP)
  intro c
  simp only [Function.comp_apply, addGateBits_encode, encode_eq_wrap, StraightLine.gates,
    Operation.gate, forest_cons, forest_nil, List.append_nil]

theorem encode_mem_FP {source radius scale shift bits exponent : List Bool → List Bool} {start m : List Bool → ℕ}
    {sample : List Bool → ℤ} (ht : source ∈ FP) (hs : UnaryFn start) (hm : UnaryFn m)
    (hsample : (fun c => (Term.const (sample c)).toData.toBits) ∈ FP)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (TermView.term (source c)).toData.size (start c) (m c) (sample c) (TermView.term (source c))
        (radius c) (scale c) (shift c) (bits c) (exponent c)))) ∈ FP := by
  have hrstart := radialStart_unary ht hs
  have hlstart := lowStart_unary ht hs hm
  have hpstart := powerStart_unary ht hs hm hR hF hb
  have hj := joinStart_unary ht hs hm hR hF hb hN
  have hq := FrozenSource.output_unary ht hs
  have hrad := SamplePowers.output_unary hm hs hrstart (constFn_mem_FP [true])
  have hlow := BoundedLow.output_unary hlstart hR hF hb
  have hpower := SamplePowers.output_unary (hm.add (UnaryFn.const 2)) hs hpstart hN
  unfold program
  apply StraightLine.encode_append_mem_FP (FrozenSource.encode_mem_FP ht hs hsample)
  simp only [frozen_next]
  apply StraightLine.encode_append_mem_FP (SamplePowers.encode_mem_FP hm hs hrstart (constFn_mem_FP [true]))
  simp only [radial_next]
  apply StraightLine.encode_append_mem_FP (BoundedLow.encode_mem_FP hq hrad hlstart hR hF hb)
  simp only [low_next]
  apply StraightLine.encode_append_mem_FP (SamplePowers.encode_mem_FP (hm.add (UnaryFn.const 2)) hs hpstart hN)
  simp only [power_next]
  apply StraightLine.encode_append_mem_FP (add_encode_mem_FP hj hlow hpower)
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  simpa only [Dyadic.gates_eq] using Dyadic.encode_mem_FP hj (hj.add (UnaryFn.const 1)) hE

end LeanCanny.ETR.ComplexCircuit.BoundedSource
