/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationFrames
public import LeanCanny.Encoding.ContextSourceTreeFold
public import LeanCanny.ETR.NNFFP

/-! # Uniform native execution of the partial homogenization tree pass -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationNative
open LeanCanny.Encoding
open Turing.MultiTapeTM
open Brackets PartialHomogenizationData

theorem combineBits_code (P : Parameters) (z : List Bool) (child parent : List Data) :
    combineBits P (pair z (pair (code P z child) (code P z parent))) = code P z (NNF.combine child parent) := by
  simp only [combineBits,pairFst_pair,pairSnd_pair,degreeFinish_code,termFinish_code]
  simp only [code,frameCode,raw,degrees,terms,pairFst_pair,pairSnd_pair,NNF.combine,List.map_cons,
    consNode_toBits]

theorem code_empty (P : Parameters) (z : List Bool) : code P z [] = frameCode 0 0 0 [] := rfl

def run (P : Parameters) (source : List Bool → List Bool) (z : List Bool) : List Bool :=
  DynamicTreeFold.encode (code P z) (TreeFold.run [] NNF.combine (source z))

theorem run_FP (P : Parameters) (hP : Access P) (source : List Bool → List Bool) (hs : source ∈ FP) :
    run P source ∈ FP := by
  let bound := fun z => 31+(source z).length*(80*P.degree z+2*P.limit z+230)
  have HB : UnaryFn bound := (UnaryFn.const 31).add ((UnaryFn.length hs).mul
    ((((UnaryFn.const 80).mul hP.degree).add ((UnaryFn.const 2).mul hP.limit)).add (UnaryFn.const 230)))
  have HP : PolyBounded List.length bound := by
    simpa only [Turing.MultiTapeTM.encBits_apply,Turing.MultiTapeTM.encUnary_apply,List.length_replicate]
      using HB.polyBounded_length
  refine DynamicTreeFold.sourceEncoded_mem_FP_context source hs (fun _ => []) (fun _ => NNF.combine)
    (code P) (fun _ => frameCode 0 0 0 []) (combineBits P) (constFn_mem_FP _) (combineBits_FP P hP)
    (fun _ => rfl) (combineBits_code P) HP ?_
  intro z t ht
  have H := DynamicTreeFold.run_encode_length_le ([] : List Data) NNF.combine (code P z)
    (40*P.degree z+P.limit z+100) (fun child parent => frameCode_growth _ _ _ child parent) t
  have HE : (code P z []).length=14 := frameCode_empty _ _ _
  rw [HE] at H
  have HK : 2*14+2*(40*P.degree z+P.limit z+100)+2 = 80*P.degree z+2*P.limit z+230 := by omega
  rw [HK] at H
  have HM := Nat.mul_le_mul_right (80*P.degree z+2*P.limit z+230) ht.length_le
  dsimp [bound]
  omega

def extract (state : List Bool) : List Bool := firstChild (terms (pairFst (state.drop 1)))

theorem extract_FP : extract ∈ FP := by
  have HF : (fun s : List Bool => pairFst (s.drop 1)) ∈ FP :=
    mem_FP_comp (f:=fun s => s.drop 1) (g:=pairFst) (drop_mem_FP id_mem_FP (UnaryFn.const 1)) pairFst_mem_FP
  have HT : (fun s : List Bool => terms (pairFst (s.drop 1))) ∈ FP :=
    mem_FP_comp (f:=fun s => pairFst (s.drop 1)) (g:=terms) HF terms_FP
  exact mem_FP_comp (f:=fun s => terms (pairFst (s.drop 1))) (g:=firstChild) HT firstChild_mem_FP

def write (P : Parameters) (source : List Bool → List Bool) (z : List Bool) : List Bool :=
  extract (run P source z)

theorem write_FP (P : Parameters) (hP : Access P) (source : List Bool → List Bool) (hs : source ∈ FP) :
    write P source ∈ FP := mem_FP_comp (run_FP P hP source hs) extract_FP

theorem write_data (P : Parameters) (source : List Bool → List Bool) (z : List Bool) (d : Data)
    (hd : source z=d.toBits) :
    write P source z = (bounded (P.parameterCount z) (P.degree z) (P.limit z) d).toBits := by
  simp [write,run,hd,TreeFold.run_toBits,NNF.foldData_identity,NNF.combine,DynamicTreeFold.encode,
    DynamicTreeFold.stackBits,extract,terms,code,frameCode,firstChild_toBits]

theorem write_term (P : Parameters) (source : List Bool → List Bool) (z : List Bool) (t : Term)
    (hs : source z=t.toData.toBits) (ht : t.degreeBound ≤ P.degree z) (hL : t.toData.size ≤ P.limit z) :
    write P source z = (PartialHomogenization.homogenize (P.parameterCount z) t).toData.toBits := by
  rw [write_data P source z t.toData hs,bounded_term _ _ _ t ht hL]

end LeanCanny.ETR.PartialHomogenizationNative
