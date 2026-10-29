/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineStageCorrect

/-! # Native generation of shared affine critical stages -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineStage
open LeanCanny.Encoding.Brackets

structure Inputs.PolyTime (F : List Bool → Inputs) : Prop where
  base : UnaryFn (fun c => (F c).base)
  start : UnaryFn (fun c => (F c).start)
  ambient : UnaryFn (fun c => (F c).ambient)
  multipliers : UnaryFn (fun c => (F c).multipliers)
  count : UnaryFn (fun c => (F c).count)
  sourceLength : UnaryFn (fun c => (F c).source.length)
  source : (fun c => encode (StraightLine.gates (F c).start (F c).source)) ∈ FP
  sourceOutput : UnaryFn (fun c => (F c).sourceOutput)
  normal : UnaryFn (fun q => (F (pairFst (pairFst q))).normal (pairSnd (pairFst q)).length (pairSnd q).length)
  level : UnaryFn (fun q => (F (pairFst q)).level (pairSnd q).length)
  active : FPPred (fun q => (F (pairFst q)).active (pairSnd q).length = true)

private theorem copyBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => copyBase (F c)) :=
  h.base.add (UnaryFn.const 1)

private theorem gradientBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => gradientBase (F c)) :=
  (copyBase_unary h).add (h.count.mul ((UnaryFn.const 16).mul (h.start.add h.sourceLength)))

private theorem heightBase_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) : UnaryFn (fun c => heightBase (F c)) :=
  (gradientBase_unary h).add (h.count.mul (((UnaryFn.const 4).mul (h.count.add (UnaryFn.const 1))).add (UnaryFn.const 3)))

private theorem gradientRow_encode_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun q => encode (StraightLine.gates (gradientStart (F (pairFst q)) (pairSnd q).length)
      (gradientRow (F (pairFst q)) (pairSnd q).length))) ∈ FP := by
  have hi := UnaryFn.length pairSnd_mem_FP
  have hn := (h.count.add (UnaryFn.const 1)).comp pairFst_mem_FP
  have hb := ((gradientBase_unary h).comp pairFst_mem_FP).add (hi.mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3)))
  have hd := GradientFamily.derivativeWire_unary ((copyBase_unary h).comp pairFst_mem_FP)
    (h.start.comp pairFst_mem_FP) hi (h.sourceOutput.comp pairFst_mem_FP) (h.sourceLength.comp pairFst_mem_FP)
  have hp := mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have he : UnaryFn (fun q => (F (pairFst (pairFst q))).normal (pairSnd q).length (pairSnd (pairFst q)).length) :=
    (h.normal.comp hp).of_eq (fun _ => by simp only [pairFst_pair, pairSnd_pair, Function.comp_apply])
  exact AffineRow.difference_encode_FP (coefficients := fun q r => (F (pairFst q)).normal r (pairSnd q).length)
    (h.base.comp pairFst_mem_FP) hb (h.multipliers.comp pairFst_mem_FP) hn hd he

private theorem heightRow_encode_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun q => encode (StraightLine.gates (heightStart (F (pairFst q)) (pairSnd q).length)
      (heightRow (F (pairFst q)) (pairSnd q).length))) ∈ FP := by
  have hi := UnaryFn.length pairSnd_mem_FP
  have hn := h.count.comp pairFst_mem_FP
  have hb := ((heightBase_unary h).comp pairFst_mem_FP).add (hi.mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3)))
  have hr := ((UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).add (UnaryFn.const 1)).mem_FP
  have hp := mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hr) pairSnd_mem_FP
  have he : UnaryFn (fun q => (F (pairFst (pairFst q))).normal ((pairSnd (pairFst q)).length + 1) (pairSnd q).length) :=
    (h.normal.comp hp).of_eq (fun _ => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate, Function.comp_apply])
  exact AffineRow.height_encode_FP (coefficients := fun q => (F (pairFst q)).normal ((pairSnd q).length + 1))
    (h.base.comp pairFst_mem_FP) hb (h.ambient.comp pairFst_mem_FP) hn h.level he

private theorem gradientPrefix_forest_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun c => forest (gradientGates (F c) (F c).count)) ∈ FP := by
  have H := flatMap_range_mem_FP (mem_FP_comp (gradientRow_encode_FP h) contents_mem_FP) h.count.mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [gradientGates_range]
  simp only [forest, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_assoc]

private theorem heightPrefix_forest_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun c => forest (heightGates (F c) (F c).count)) ∈ FP := by
  have H := flatMap_range_mem_FP (mem_FP_comp (heightRow_encode_FP h) contents_mem_FP) h.count.mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [heightGates_range]
  simp only [forest, List.map_flatMap, List.flatten_eq_flatMap, List.flatMap_assoc]

theorem program_encode_FP {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    (fun c => encode (gates (F c))) ∈ FP := by
  have hg := GradientFamily.encode_mem_FP h.base (copyBase_unary h) h.start h.ambient h.count h.sourceLength h.source
  have hz := constantGateBits_mem_FP h.base (constFn_mem_FP (Term.const 0).toData.toBits)
  have H := mem_FP_comp (appendFn_mem_FP hz (appendFn_mem_FP (mem_FP_comp hg contents_mem_FP)
    (appendFn_mem_FP (gradientPrefix_forest_FP h) (heightPrefix_forest_FP h)))) wrap_mem_FP
  apply mem_FP_of_eq H
  intro c
  simp only [Function.comp_apply, contents_encode, constantGateBits_encode]
  rw [encode_eq_wrap, gates_eq]
  simp only [forest_cons, forest_append]

theorem length_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    UnaryFn (fun c => (program (F c)).length) :=
  ((((UnaryFn.const 1).add (h.count.mul ((UnaryFn.const 16).mul (h.start.add h.sourceLength)))).add
    (h.count.mul (((UnaryFn.const 4).mul (h.count.add (UnaryFn.const 1))).add (UnaryFn.const 3)))).add
    (h.count.mul (((UnaryFn.const 4).mul h.count).add (UnaryFn.const 3)))).of_eq (fun _ => (program_length _).symm)

theorem output_unary {F : List Bool → Inputs} (h : Inputs.PolyTime F) :
    UnaryFn (fun q => output (F (pairFst q)) (pairSnd q).length) := by
  have hq := UnaryFn.length pairSnd_mem_FP
  have hn := h.count.comp pairFst_mem_FP
  have hn1 := hn.add (UnaryFn.const 1)
  have hG := (((gradientBase_unary h).comp pairFst_mem_FP).add
    (hq.mul (((UnaryFn.const 4).mul hn1).add (UnaryFn.const 3)))).add
      (((UnaryFn.const 4).mul hn1).add (UnaryFn.const 2))
  have hS := GradientFamily.valueWire_unary ((copyBase_unary h).comp pairFst_mem_FP)
    (h.start.comp pairFst_mem_FP) (UnaryFn.const 0) (h.sourceOutput.comp pairFst_mem_FP) (h.sourceLength.comp pairFst_mem_FP)
  have hr := hq.sub hn1
  have hH := (((heightBase_unary h).comp pairFst_mem_FP).add
    (hr.mul (((UnaryFn.const 4).mul hn).add (UnaryFn.const 3)))).add
      (((UnaryFn.const 4).mul hn).add (UnaryFn.const 2))
  have hU := (h.multipliers.comp pairFst_mem_FP).add (hr.add (UnaryFn.const 1))
  have hp := h.active.comp (mem_FP_pair pairFst_mem_FP hr.mem_FP)
  have ha : FPPred (fun q => (F (pairFst q)).active ((pairSnd q).length - ((F (pairFst q)).count + 1)) = true) :=
    hp.of_iff (fun _ => by simp only [pairFst_pair, pairSnd_pair, List.length_replicate])
  exact (UnaryFn.ite (FPPred.lt hq hn) hG (UnaryFn.ite (FPPred.eq hq hn) hS (UnaryFn.ite ha hH hU))).of_eq
    (fun _ => by dsimp [output, gradientOutput, heightOutput, gradientStart, heightStart, AffineRow.output, AffineRow.stride, sourceOutput, KernelRow.criticalWire]; split_ifs <;> omega)

end LeanCanny.ETR.ComplexCircuit.AffineStage
