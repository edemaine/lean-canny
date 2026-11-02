/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationData
public import LeanCanny.Encoding.ContextTreeFold

/-! # Native local operations for the annotated homogenization pass -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationNative
open LeanCanny.Encoding
open Brackets

structure Parameters where
  parameterCount : List Bool → ℕ
  degree : List Bool → ℕ
  limit : List Bool → ℕ
structure Access (P : Parameters) : Prop where
  parameterCount : UnaryFn P.parameterCount
  degree : UnaryFn P.degree
  limit : UnaryFn P.limit

def raw (frame : List Bool) := pairFst frame
def degrees (frame : List Bool) := pairFst (pairSnd frame)
def terms (frame : List Bool) := pairSnd (pairSnd frame)
def context (packet : List Bool) := pairFst packet
def frame (packet : List Bool) := pairSnd packet

def variableIndex (packet : List Bool) := Codec.unaryValue (NNF.second (raw (frame packet)))
def leftDegree (packet : List Bool) := Codec.unaryValue (NNF.second (degrees (frame packet)))
def rightDegree (packet : List Bool) := Codec.unaryValue (NNF.third (degrees (frame packet)))

theorem raw_FP : raw ∈ FP := pairFst_mem_FP
theorem degrees_FP : degrees ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem terms_FP : terms ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem frame_FP : frame ∈ FP := pairSnd_mem_FP
theorem context_FP : context ∈ FP := pairFst_mem_FP

attribute [local irreducible] raw degrees terms frame context NNF.second NNF.third

theorem variableIndex_unary : UnaryFn variableIndex := by
  have H : (fun p => NNF.second (raw (frame p))) ∈ FP :=
    mem_FP_comp (f:=fun p => raw (frame p)) (g:=NNF.second)
      (mem_FP_comp (f:=frame) (g:=raw) frame_FP raw_FP) NNF.second_mem_FP
  exact UnaryFn.comp (f:=Codec.unaryValue) (g:=fun p => NNF.second (raw (frame p))) Codec.unaryValue_unary H

theorem leftDegree_unary : UnaryFn leftDegree := by
  have H : (fun p => NNF.second (degrees (frame p))) ∈ FP :=
    mem_FP_comp (f:=fun p => degrees (frame p)) (g:=NNF.second)
      (mem_FP_comp (f:=frame) (g:=degrees) frame_FP degrees_FP) NNF.second_mem_FP
  exact UnaryFn.comp (f:=Codec.unaryValue) (g:=fun p => NNF.second (degrees (frame p))) Codec.unaryValue_unary H

theorem rightDegree_unary : UnaryFn rightDegree := by
  have H : (fun p => NNF.third (degrees (frame p))) ∈ FP :=
    mem_FP_comp (f:=fun p => degrees (frame p)) (g:=NNF.third)
      (mem_FP_comp (f:=frame) (g:=degrees) frame_FP degrees_FP) NNF.third_mem_FP
  exact UnaryFn.comp (f:=Codec.unaryValue) (g:=fun p => NNF.third (degrees (frame p))) Codec.unaryValue_unary H

attribute [local irreducible] variableIndex leftDegree rightDegree

def degreeFinish (P : Parameters) (packet : List Bool) : ℕ :=
  if NNF.HasOne 1 (raw (frame packet)) then
    if variableIndex packet < P.parameterCount (context packet) then 0 else min 1 (P.degree (context packet))
  else if NNF.HasTwo 2 (raw (frame packet)) then max (leftDegree packet) (rightDegree packet)
  else if NNF.HasTwo 3 (raw (frame packet)) then
    min (leftDegree packet+rightDegree packet) (P.degree (context packet)) else 0

theorem degreeFinish_unary (P : Parameters) (hP : Access P) : UnaryFn (degreeFinish P) := by
  have HR : (fun p => raw (frame p)) ∈ FP := mem_FP_comp (f:=frame) (g:=raw) frame_FP raw_FP
  have HD := hP.degree.comp context_FP
  have HK := hP.parameterCount.comp context_FP
  exact UnaryFn.ite ((NNF.hasOne_fppred 1).comp HR)
    (UnaryFn.ite (FPPred.lt variableIndex_unary HK) (UnaryFn.const 0) ((UnaryFn.const 1).min HD))
    (UnaryFn.ite ((NNF.hasTwo_fppred 2).comp HR) (leftDegree_unary.max rightDegree_unary)
      (UnaryFn.ite ((NNF.hasTwo_fppred 3).comp HR) ((leftDegree_unary.add rightDegree_unary).min HD) (UnaryFn.const 0)))

def leftPower (packet : List Bool) : ℕ := max (leftDegree packet) (rightDegree packet)-leftDegree packet
def rightPower (packet : List Bool) : ℕ := max (leftDegree packet) (rightDegree packet)-rightDegree packet

def termFinish (P : Parameters) (packet : List Bool) : List Bool :=
  if (raw (frame packet)).length ≤ P.limit (context packet) then
    if NNF.HasOne 0 (raw (frame packet)) then raw (frame packet)
    else if NNF.HasOne 1 (raw (frame packet)) then (Term.var (variableIndex packet+1)).toData.toBits
    else if NNF.HasTwo 2 (raw (frame packet)) then
      Codec.taggedTwo 2
        (Codec.taggedTwo 3 ((Term.var 0).power (leftPower packet)).toData.toBits (NNF.second (terms (frame packet))))
        (Codec.taggedTwo 3 ((Term.var 0).power (rightPower packet)).toData.toBits (NNF.third (terms (frame packet))))
    else if NNF.HasTwo 3 (raw (frame packet)) then
      Codec.taggedTwo 3 (NNF.second (terms (frame packet))) (NNF.third (terms (frame packet)))
    else (Term.const 0).toData.toBits
  else (Term.const 0).toData.toBits

theorem termFinish_FP (P : Parameters) (hP : Access P) : termFinish P ∈ FP := by
  have HR : (fun p => raw (frame p)) ∈ FP := mem_FP_comp (f:=frame) (g:=raw) frame_FP raw_FP
  have HT : (fun p => terms (frame p)) ∈ FP := mem_FP_comp (f:=frame) (g:=terms) frame_FP terms_FP
  have HL : (fun p => NNF.second (terms (frame p))) ∈ FP := mem_FP_comp (f:=fun p => terms (frame p)) (g:=NNF.second) HT NNF.second_mem_FP
  have HU : (fun p => NNF.third (terms (frame p))) ∈ FP := mem_FP_comp (f:=fun p => terms (frame p)) (g:=NNF.third) HT NNF.third_mem_FP
  have HP (f : List Bool → ℕ) (hf : UnaryFn f) :
      (fun q => ((Term.var 0).power (f q)).toData.toBits) ∈ FP := by
    apply mem_FP_of_eq (TermPower.write_mem_FP (constFn_mem_FP (Term.var 0).toData.toBits) hf)
    intro q
    rw [TermPower.write_correct,TermView.term_toBits]
  have HPL := HP leftPower ((leftDegree_unary.max rightDegree_unary).sub leftDegree_unary)
  have HPR := HP rightPower ((leftDegree_unary.max rightDegree_unary).sub rightDegree_unary)
  have HV := mem_FP_of_eq (Term.variableBits_mem_FP (variableIndex_unary.add (UnaryFn.const 1)))
    (fun _ => Term.variableBits_eq _)
  have HA := Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 HPL HL) (Codec.taggedTwo_mem_FP 3 HPR HU)
  have HM := Codec.taggedTwo_mem_FP 3 HL HU
  exact (FPPred.le (UnaryFn.length HR) (hP.limit.comp context_FP)).ite_mem_FP
    (((NNF.hasOne_fppred 0).comp HR).ite_mem_FP HR
      (((NNF.hasOne_fppred 1).comp HR).ite_mem_FP HV
        (((NNF.hasTwo_fppred 2).comp HR).ite_mem_FP HA
          (((NNF.hasTwo_fppred 3).comp HR).ite_mem_FP HM (constFn_mem_FP (Term.const 0).toData.toBits)))))
    (constFn_mem_FP (Term.const 0).toData.toBits)

def combineBits (P : Parameters) (packet : List Bool) : List Bool :=
  let z := pairFst packet
  let child := pairFst (pairSnd packet)
  let parent := pairSnd (pairSnd packet)
  pair (consNode (raw child) (raw parent))
    (pair (consNode (Codec.unary (degreeFinish P (pair z child))).toBits (degrees parent))
      (consNode (termFinish P (pair z child)) (terms parent)))

theorem combineBits_FP (P : Parameters) (hP : Access P) : combineBits P ∈ FP := by
  have HC := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have HQ := mem_FP_pair pairFst_mem_FP HC
  have HD := Codec.unary_toBits_mem_FP ((degreeFinish_unary P hP).comp HQ)
  have HT := mem_FP_comp HQ (termFinish_FP P hP)
  exact mem_FP_pair
    (consNode_mem_FP (mem_FP_comp HC raw_FP) (mem_FP_comp HP raw_FP))
    (mem_FP_pair (consNode_mem_FP HD (mem_FP_comp HP degrees_FP))
      (consNode_mem_FP HT (mem_FP_comp HP terms_FP)))

end LeanCanny.ETR.PartialHomogenizationNative
