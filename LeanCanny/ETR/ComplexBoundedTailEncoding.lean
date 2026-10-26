/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexBoundedTail

/-! # Native bounds for the variable-coordinate bounded source tail -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BoundedTail
open LeanCanny.Encoding.Brackets

theorem lowStart_unary {start m : List Bool → ℕ} (hs : UnaryFn start) (hm : UnaryFn m) :
    UnaryFn (fun c => lowStart (start c) (m c)) :=
  ((hs.add (UnaryFn.const 1)).add ((hm.add (UnaryFn.const 1)).mul (UnaryFn.const 8))).of_eq (fun _ => rfl)
theorem powerStart_unary {start m : List Bool → ℕ} {radius scale shift : List Bool → List Bool}
    (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) :
    UnaryFn (fun c => powerStart (start c) (m c) (radius c) (scale c) (shift c)) :=
  ((BoundedLow.output_unary (lowStart_unary hs hm) hR hF hb).add (UnaryFn.const 1)).of_eq (fun _ => rfl)
theorem joinStart_unary {start m : List Bool → ℕ} {radius scale shift bits : List Bool → List Bool}
    (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) :
    UnaryFn (fun c => joinStart (start c) (m c) (radius c) (scale c) (shift c) (bits c)) :=
  (((powerStart_unary hs hm hR hF hb).add (UnaryFn.const 1)).add ((hm.add (UnaryFn.const 3)).mul
    (((UnaryFn.const 2).mul (UnaryFn.length hN)).add (UnaryFn.const 6)))).of_eq (fun _ => rfl)
theorem output_unary {start m : List Bool → ℕ} {radius scale shift bits exponent : List Bool → List Bool}
    (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP)
    (hE : exponent ∈ FP) : UnaryFn (fun c => output (start c) (m c) (radius c) (scale c) (shift c) (bits c) (exponent c)) :=
  ((Dyadic.productWire_unary ((joinStart_unary hs hm hR hF hb hN).add (UnaryFn.const 1)) hE).add
    (UnaryFn.const 2)).of_eq (fun _ => rfl)
theorem energyOutput_unary {start m : List Bool → ℕ} {radius : List Bool → List Bool}
    (hs : UnaryFn start) (hm : UnaryFn m) (hR : radius ∈ FP) :
    UnaryFn (fun c => energyOutput (start c) (m c) (radius c)) :=
  ((BoundedLow.energyStart_unary (lowStart_unary hs hm) hR).add (UnaryFn.const 5)).of_eq (fun _ => rfl)
theorem length_unary {source sample start m : List Bool → ℕ} {radius scale shift bits exponent : List Bool → List Bool}
    (hm : UnaryFn m) (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    UnaryFn (fun c => (program (source c) (sample c) (start c) (m c) (radius c) (scale c) (shift c) (bits c) (exponent c)).length) :=
  ((((((((UnaryFn.const 8).mul (hm.add (UnaryFn.const 1))).add ((UnaryFn.const 2).mul (UnaryFn.length hR))).add
    ((UnaryFn.const 2).mul (UnaryFn.length hF))).add ((UnaryFn.const 2).mul (UnaryFn.length hb))).add
      ((hm.add (UnaryFn.const 3)).mul (((UnaryFn.const 2).mul (UnaryFn.length hN)).add (UnaryFn.const 6)))).add
        ((UnaryFn.const 2).mul (UnaryFn.length hE))).add (UnaryFn.const 24)).of_eq
          (fun _ => (program_length _ _ _ _ _ _ _ _ _).symm)

private theorem add_encode_mem_FP {start left right : List Bool → ℕ}
    (hs : UnaryFn start) (hl : UnaryFn left) (hr : UnaryFn right) :
    (fun c => encode (StraightLine.gates (start c) [.add (left c) (right c)])) ∈ FP := by
  apply mem_FP_of_eq (mem_FP_comp (arithmeticGateBits_mem_FP 1 hs hl hr) wrap_mem_FP)
  intro c
  simp only [Function.comp_apply, addGateBits_encode, encode_eq_wrap, StraightLine.gates,
    Operation.gate, forest_cons, forest_nil, List.append_nil]

theorem encode_mem_FP {source sample start m : List Bool → ℕ} {radius scale shift bits exponent : List Bool → List Bool}
    (hq : UnaryFn source) (ha : UnaryFn sample) (hs : UnaryFn start) (hm : UnaryFn m)
    (hR : radius ∈ FP) (hF : scale ∈ FP) (hb : shift ∈ FP) (hN : bits ∈ FP) (hE : exponent ∈ FP) :
    (fun c => encode (StraightLine.gates (start c)
      (program (source c) (sample c) (start c) (m c) (radius c) (scale c) (shift c) (bits c) (exponent c)))) ∈ FP := by
  have hl := lowStart_unary hs hm
  have hp := powerStart_unary hs hm hR hF hb
  have hj := joinStart_unary hs hm hR hF hb hN
  have hrad := SamplePowers.output_unary hm ha hs (constFn_mem_FP [true])
  have hlow := BoundedLow.output_unary hl hR hF hb
  have hpower := SamplePowers.output_unary (hm.add (UnaryFn.const 2)) ha hp hN
  unfold program
  apply StraightLine.encode_append_mem_FP (SamplePowers.encode_mem_FP hm ha hs (constFn_mem_FP [true]))
  simp only [radial_next]
  apply StraightLine.encode_append_mem_FP (BoundedLow.encode_mem_FP hq hrad hl hR hF hb)
  simp only [low_next]
  apply StraightLine.encode_append_mem_FP (SamplePowers.encode_mem_FP (hm.add (UnaryFn.const 2)) ha hp hN)
  simp only [power_next]
  apply StraightLine.encode_append_mem_FP (add_encode_mem_FP hj hlow hpower)
  simp only [List.length_cons, List.length_nil, Nat.zero_add]
  simpa only [Dyadic.gates_eq] using Dyadic.encode_mem_FP hj (hj.add (UnaryFn.const 1)) hE

end LeanCanny.ETR.ComplexCircuit.BoundedTail
