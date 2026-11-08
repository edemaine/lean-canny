/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryNativeFrontier
/-! # Native reachability in the original fixed-width frontier graph -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryNativeGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CanonicalAuxiliaryNativeFrontier.edge

variable (D:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.language)
include D in
theorem edges_reindex (f:List Bool→List Bool) (hf:f∈FP):ComputableInPolySpace
    (fun p:List Bool×List Bool×List Bool=>CanonicalAuxiliaryNativeFrontier.edge (f p.1) p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool:=by
  have E:=CanonicalAuxiliaryNativeFrontier.edge_computable D
  have HP:=ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have HS:=ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  exact E.comp (.of_tidyPolyTime ((hf.comp HP).prod (HS.fst'.prod HS.snd')))
include D in
theorem connected_computable:ComputableInPolySpace
    (fun c=>decide (ImplicitGraph.Connected (CanonicalAuxiliaryNativeFrontier.edge c)
      (CanonicalAuxiliaryNativeFrontier.valid c) (CanonicalAuxiliaryNativeFrontier.width c))) encBits encBool:=
  ImplicitGraph.connected_computable (CanonicalAuxiliaryNativeFrontier.edge_computable D)
    CanonicalAuxiliaryNativeFrontier.valid_computable CanonicalAuxiliaryNativeFrontier.width_unary

noncomputable def width (q:List Bool):=CanonicalAuxiliaryNativeFrontier.width (pairFst q)
noncomputable def source (q:List Bool):=ImplicitGraph.word (width q) (Nat.fromBitsLE (pairFst (pairSnd q)))
noncomputable def target (q:List Bool):=ImplicitGraph.word (width q) (Nat.fromBitsLE (pairSnd (pairSnd q)))
noncomputable def Reachable (q:List Bool):Prop:=ImplicitGraph.Reachable
  (CanonicalAuxiliaryNativeFrontier.edge (pairFst q)) (CanonicalAuxiliaryNativeFrontier.valid (pairFst q))
    (width q) (source q) (target q)
theorem width_unary:UnaryFn width:=CanonicalAuxiliaryNativeFrontier.width_unary.comp pairFst_mem_FP
theorem source_FP:source∈FP:=ImplicitGraph.word_computable width_unary
  (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
theorem target_FP:target∈FP:=ImplicitGraph.word_computable width_unary
  (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
include D in
theorem reachable_computable:ComputableInPolySpace (fun q=>decide (Reachable q)) encBits encBool:=by
  have HP:=ComputableTidilyInPolyTime.fst encBits encBits
  have HS:=ComputableTidilyInPolyTime.snd encBits encBits
  have HV:=CanonicalAuxiliaryNativeFrontier.valid_computable.comp (.of_tidyPolyTime ((pairFst_mem_FP.comp HP).prod HS))
  exact ImplicitGraph.reachable_computable (edges_reindex D pairFst pairFst_mem_FP) HV width_unary
    (.of_tidyPolyTime source_FP) (.of_tidyPolyTime target_FP) (fun q=>ImplicitGraph.length_word _ _) (fun q=>ImplicitGraph.length_word _ _)
include D in
theorem evaluator:SpaceFunction (fun q=>[decide (Reachable q)]):=by
  obtain ⟨S,hS,h⟩:=(reachable_computable D).exists_inSpace
  exact ⟨.of_inSpace hS (h.of_enc_eq (fun q=>rfl))⟩

theorem reachable_packet (c a b:List Bool) (ha:a.length=CanonicalAuxiliaryNativeFrontier.width c)
    (hb:b.length=CanonicalAuxiliaryNativeFrontier.width c):Reachable (pair c (pair a b)) ↔
    ImplicitGraph.Reachable (CanonicalAuxiliaryNativeFrontier.edge c) (CanonicalAuxiliaryNativeFrontier.valid c)
      (CanonicalAuxiliaryNativeFrontier.width c) a b:=by
  have HS:ImplicitGraph.word (CanonicalAuxiliaryNativeFrontier.width c) (Nat.fromBitsLE a)=a:=by
    rw [←ha,ImplicitGraph.word_fromBitsLE]
  have HT:ImplicitGraph.word (CanonicalAuxiliaryNativeFrontier.width c) (Nat.fromBitsLE b)=b:=by
    rw [←hb,ImplicitGraph.word_fromBitsLE]
  simp only [Reachable,width,source,target,pairFst_pair,pairSnd_pair,HS,HT]

private theorem edges_eq (d:Description) (hd:d.WellFormed):
    CanonicalAuxiliaryNativeFrontier.edge (CanonicalSignRefinement.original d)=CanonicalAuxiliaryBitFrontier.edge d:=by
  funext a b
  exact CanonicalAuxiliaryNativeFrontier.edge_eq d hd a b

theorem connected_iff (d:Description) (hd:d.WellFormed):
    ImplicitGraph.Connected (CanonicalAuxiliaryNativeFrontier.edge (CanonicalSignRefinement.original d))
      (CanonicalAuxiliaryNativeFrontier.valid (CanonicalSignRefinement.original d))
      (CanonicalAuxiliaryNativeFrontier.width (CanonicalSignRefinement.original d)) ↔
        (Input.whole d).encode∈connectedLanguage:=by
  rw [edges_eq d hd]
  exact (CanonicalAuxiliaryBitFrontier.connected_language_iff d hd).symm

theorem reachable_encoded_iff (d:Description) (hd:d.WellFormed) (i j:CanonicalAuxiliaryCandidateCover.Index d)
    (hi:CanonicalAuxiliaryProjectedSamples.Good d i) (hj:CanonicalAuxiliaryProjectedSamples.Good d j):
    ImplicitGraph.Reachable (CanonicalAuxiliaryNativeFrontier.edge (CanonicalSignRefinement.original d))
      (CanonicalAuxiliaryNativeFrontier.valid (CanonicalSignRefinement.original d))
      (CanonicalAuxiliaryNativeFrontier.width (CanonicalSignRefinement.original d))
        (CanonicalAuxiliaryCandidateCover.encode d i) (CanonicalAuxiliaryCandidateCover.encode d j) ↔
          CanonicalAuxiliaryCandidateCover.walk d i j:=by
  let x:=CanonicalAuxiliaryCandidateCover.sample d hd i hi
  let y:=CanonicalAuxiliaryCandidateCover.sample d hd j hj
  have HX:x∈CanonicalAuxiliaryCandidateCover.piece d i:=CanonicalAuxiliaryCandidateCover.sample_mem d hd i hi
  have HY:y∈CanonicalAuxiliaryCandidateCover.piece d j:=CanonicalAuxiliaryCandidateCover.sample_mem d hd j hj
  have HXi:x∈CanonicalAuxiliaryBitFrontier.piece d (CanonicalAuxiliaryCandidateCover.vertex d i):=by
    rw [CanonicalAuxiliaryBitFrontier.piece_encode d i ⟨x,HX⟩ hd]
    exact HX
  have HYj:y∈CanonicalAuxiliaryBitFrontier.piece d (CanonicalAuxiliaryCandidateCover.vertex d j):=by
    rw [CanonicalAuxiliaryBitFrontier.piece_encode d j ⟨y,HY⟩ hd]
    exact HY
  have HR:=(CanonicalAuxiliaryBitFrontier.cover d hd).joinedIn_iff_reachable
    (CanonicalAuxiliaryCandidateCover.encode_length d i) (CanonicalAuxiliaryCandidateCover.encode_length d j) HXi HYj
  have HT:=FrontierCover.joinedIn_iff_reachable (CanonicalAuxiliaryCandidateCover.piece d)
    (CanonicalAuxiliaryCandidateCover.covers d hd) (CanonicalAuxiliaryCandidateCover.accessible d hd) HX HY
  rw [edges_eq d hd]
  exact HR.symm.trans HT
end LeanCanny.Connectivity.CanonicalAuxiliaryNativeGraph
