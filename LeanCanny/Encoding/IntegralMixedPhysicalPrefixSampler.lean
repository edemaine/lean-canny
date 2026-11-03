/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.NoInfinitySquareWordWidth
public import LeanCanny.Encoding.SquareSampleCompleteNaturality
/-! # Original native complete samplers at every positive fixed-cap prefix

The context is the unchanged prepared root paired with a unary birth minus
one. Only the saved prefix changes; the root, horizon and scalar width do not.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPrefixSampler
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def stage (P : Parameters) (c : List Bool):=min ((pairSnd c).length+1) (P.cap (pairFst c)+1)
def key (P : Parameters) (c : List Bool):=IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst c) (stage P c) []
def packet (root : List Bool) (birth : ℕ):=pair root (List.replicate (birth-1) true)

theorem stage_unary (P : Parameters) (a : Access P) : UnaryFn (stage P):=
 ((UnaryFn.length pairSnd_mem_FP).add (UnaryFn.const 1)).min
   ((a.cap.comp pairFst_mem_FP).add (UnaryFn.const 1))
theorem key_FP (P : Parameters) (a : Access P) : key P∈FP:=
 mem_FP_pair pairFst_mem_FP (mem_FP_pair (BinaryFn.ofUnary (stage_unary P a)).bits_mem_FP (constFn_mem_FP []))
theorem stage_pos (P : Parameters) (c : List Bool) : 0<stage P c:=
 lt_min (Nat.succ_pos _) (Nat.succ_pos _)
theorem stage_le (P : Parameters) (c : List Bool) : stage P c≤P.cap (pairFst c)+1:=min_le_right _ _

theorem key_birth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
 (family P D H).birth (key P c)=stage P c:=
 (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).trans
   (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P (pairFst c) (stage P c) [] (stage_le P c))
theorem positive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
 0<(family P D H).birth (key P c):=by rw [key_birth];exact stage_pos P c

theorem key_packet (P : Parameters) (root : List Bool) (b : ℕ) (hb : 0<b) (hc : b≤P.cap root+1) :
 key P (packet root b)=IntegralMixedFramedHistoryFamilyBits.keyAt root b []:=by
 unfold key stage packet
 simp only [pairFst_pair,pairSnd_pair,List.length_replicate,Nat.sub_add_cancel hb,min_eq_left hc]

variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable abbrev input:=IntegralFramedPhysicalSquare.input
 (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
 (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
 (bank hn ht ha hR outer).bounds (key (bank hn ht ha hR outer).parameters)
 (positive (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data)

attribute [local irreducible] bank native tables

theorem access : (input hn ht ha hR outer).Access:=by
 let B:=bank hn ht ha hR outer
 let A:=native hn ht ha hR outer
 exact IntegralFramedPhysicalSquare.native_access B.parameters A.parameters B.plan B.data
   (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
   B.nodes B.factor B.seed B.bounds A.nodes A.factor A.seed (key B.parameters) (key_FP B.parameters A.parameters)
   (positive B.parameters B.plan B.data) A.liftedData A.controls A.bounds

theorem width_unary : UnaryFn (SquareSampleCompleteVertices.width (input hn ht ha hR outer)):=
 SquareSampleCompleteVertices.width_unary (access hn ht ha hR outer)

theorem at_positive (root : List Bool) (b : ℕ) (hb : 0<b)
    (hc : b≤(bank hn ht ha hR outer).parameters.cap root+1) :
    0<(family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).birth (IntegralMixedFramedHistoryFamilyBits.keyAt root b []):=by
 rw [IntegralMixedFramedHistoryFamilyBits.family_birth,
   IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ root b [] hc]
 exact hb

noncomputable abbrev atPrefix (root : List Bool) (b : ℕ) (hb : 0<b)
    (hc : b≤(bank hn ht ha hR outer).parameters.cap root+1):=
 IntegralFramedPhysicalSquare.input (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
   (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
   (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
   (fun _=>IntegralMixedFramedHistoryFamilyBits.keyAt root b []) (fun _=>at_positive hn ht ha hR outer root b hb hc)

private theorem input_key_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    {f g : List Bool→List Bool} (he : f=g)
    (hf : ∀c,0<(family P D H).birth (f c)) (hg : ∀c,0<(family P D H).birth (g c)) :
    IntegralFramedPhysicalSquare.input P D H L F C hs f hf=IntegralFramedPhysicalSquare.input P D H L F C hs g hg:=by
 cases he
 rfl

theorem input_packet (root : List Bool) (b : ℕ) (hb : 0<b)
    (hc : b≤(bank hn ht ha hR outer).parameters.cap root+1) :
    SquareSampleInput.comp (input hn ht ha hR outer) (fun _=>packet root b)=
      atPrefix hn ht ha hR outer root b hb hc:=by
 have HE : (fun _ : List Bool=>key (bank hn ht ha hR outer).parameters (packet root b))=
     (fun _ : List Bool=>IntegralMixedFramedHistoryFamilyBits.keyAt root b []):=funext (fun _=>key_packet _ root b hb hc)
 change IntegralFramedPhysicalSquare.input (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
   (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
   (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
   (fun _=>key (bank hn ht ha hR outer).parameters (packet root b))
     (fun _=>positive (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
       (bank hn ht ha hR outer).data (packet root b))=_
 exact input_key_congr _ _ _ _ _ _ _ HE _ _

theorem width_packet (root : List Bool) (b : ℕ) (hb : 0<b)
    (hc : b≤(bank hn ht ha hR outer).parameters.cap root+1) (u : List Bool) :
    SquareSampleCompleteVertices.width (atPrefix hn ht ha hR outer root b hb hc) u=
      SquareSampleCompleteVertices.width (input hn ht ha hR outer) (packet root b):=by
 rw [←input_packet hn ht ha hR outer root b hb hc]
 exact SquareSampleCompleteNaturality.complete_width_comp _ _ _

end LeanCanny.Encoding.IntegralMixedPhysicalPrefixSampler
