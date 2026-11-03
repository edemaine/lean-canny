/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureCode
/-! # Original native byte bounds for midpoint signature features -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedChronologicalMidpointSignature
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def featureBound (cap : ℕ):=3*cap.size+6
def wordBound (n birth : ℕ):=(2*featureBound (birth+n+1)+2)*(n+1)

theorem feature_size {cap : ℕ} (s : Feature cap) : (featureWord s).length≤featureBound cap :=by
  cases s with
  | producer a=>
    have H:=Nat.size_le_size a.isLt.le
    simp only [featureWord,producerWord,pair_length,List.length_nil,Nat.mul_zero,zero_add,
      BinaryNatCode.length_encode,featureBound]
    omega
  | mean a b=>
    have HA:=Nat.size_le_size a.isLt.le
    have HB:=Nat.size_le_size b.isLt.le
    simp only [featureWord,meanWord,pair_length,List.length_cons,List.length_nil,
      BinaryNatCode.length_encode,featureBound]
    omega

theorem word_size {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (a b : Fin birth) :
    (code n birth (IntegralMixedChronologicalFrameCode.labels d) a.val b.val).length≤wordBound n birth :=by
  have HS : (birth+freeCount d).size≤(birth+n+1).size:=by
    apply Nat.size_le_size
    unfold freeCount
    omega
  have HF (i : Fin (n+1)) :
      (entry n birth (IntegralMixedChronologicalFrameCode.labels d) a.val b.val i.val).length≤
        featureBound (birth+n+1) :=by
    rw [entry_actual]
    exact (feature_size _).trans (by unfold featureBound;omega)
  have H:=WordList.length_le ((List.range (n+1)).map
    (entry n birth (IntegralMixedChronologicalFrameCode.labels d) a.val b.val))
    (featureBound (birth+n+1)) (by
      intro w hw
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hw
      exact HF ⟨i,List.mem_range.mp hi⟩)
  simpa only [code,List.length_map,List.length_range,wordBound] using H

theorem wordBound_unary {n birth : List Bool→ℕ} (hn : UnaryFn n) (hb : BinaryFn birth) :
    UnaryFn (fun q=>wordBound (n q) (birth q)) :=by
  have HC:=(hb.add (BinaryFn.ofUnary hn)).add (BinaryFn.const 1)
  have HS : UnaryFn (fun q=>(birth q+n q+1).size):=
    (UnaryFn.length HC.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (((UnaryFn.const 3).mul HS).add (UnaryFn.const 6))).add
    (UnaryFn.const 2)).mul (hn.add (UnaryFn.const 1))

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureCode
