/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineLevelCorrect

/-! # Native generation of constant, height, and midpoint levels -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineLevel
open LeanCanny.Encoding.Brackets

structure Inputs.PolyTime (F : List Bool → Inputs) : Prop where
  base : UnaryFn (fun c => (F c).base)
  count : UnaryFn (fun c => (F c).count)
  left : UnaryFn (fun c => (F c).left)
  right : UnaryFn (fun c => (F c).right)
  mode : UnaryFn (fun c => (F c).mode)
  constant : (fun c => (Term.const (F c).constant).toData.toBits) ∈ FP
  normal : (fun q => (Term.const ((F (pairFst q)).normal (pairSnd q).length)).toData.toBits) ∈ FP

private theorem constantWire_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => constantWire (F c)) :=
  h.base.add (UnaryFn.const 1)
private theorem tableBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => tableBase (F c)) :=
  h.base.add (UnaryFn.const 2)
private theorem leftBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => leftBase (F c)) :=
  (tableBase_unary h).add h.count
private theorem rightBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => rightBase (F c)) :=
  (leftBase_unary h).add (((UnaryFn.const 4).mul h.count).add (UnaryFn.const 3))
private theorem sumOutput_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => sumOutput (F c)) :=
  (rightBase_unary h).add (((UnaryFn.const 4).mul h.count).add (UnaryFn.const 3))
private theorem leftOutput_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => leftOutput (F c)) :=
  ((leftBase_unary h).add ((UnaryFn.const 4).mul h.count)).add (UnaryFn.const 2)
private theorem rightOutput_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => rightOutput (F c)) :=
  ((rightBase_unary h).add ((UnaryFn.const 4).mul h.count)).add (UnaryFn.const 2)

theorem program_encode_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun c => encode (gates (F c))) ∈ FP := by
  have ht := ConstantTable.encode_FP (value := fun c => (F c).normal) (tableBase_unary h) h.count h.normal
  have he := ((tableBase_unary h).comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP)
  have hl := AffineRow.height_encode_FP (coefficients := fun c i => tableBase (F c) + i)
    h.base (leftBase_unary h) h.left h.count h.base he
  have hr := AffineRow.height_encode_FP (coefficients := fun c i => tableBase (F c) + i)
    h.base (rightBase_unary h) h.right h.count h.base he
  have hz := constantGateBits_mem_FP h.base (constFn_mem_FP (Term.const 0).toData.toBits)
  have hc := constantGateBits_mem_FP (constantWire_unary h) h.constant
  have ha := arithmeticGateBits_mem_FP 1 (sumOutput_unary h) (leftOutput_unary h) (rightOutput_unary h)
  have H := mem_FP_comp (appendFn_mem_FP hz (appendFn_mem_FP hc
    (appendFn_mem_FP (mem_FP_comp ht contents_mem_FP) (appendFn_mem_FP (mem_FP_comp hl contents_mem_FP)
      (appendFn_mem_FP (mem_FP_comp hr contents_mem_FP) ha))))) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode, addGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest_cons, forest_append, forest_nil, List.append_nil]
  rfl

theorem length_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => (program (F c)).length) :=
  (((UnaryFn.const 9).mul h.count).add (UnaryFn.const 9)).of_eq (fun _ => (program_length _).symm)

theorem output_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => output (F c)) :=
  UnaryFn.ite (FPPred.eq h.mode (UnaryFn.const 1)) (leftOutput_unary h)
    (UnaryFn.ite (FPPred.eq h.mode (UnaryFn.const 2)) (sumOutput_unary h) (constantWire_unary h))

end LeanCanny.ETR.ComplexCircuit.AffineLevel
