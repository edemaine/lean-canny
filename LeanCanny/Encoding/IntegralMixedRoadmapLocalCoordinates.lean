/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
/-! # Free coordinates are the actual MID and child capture fields -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedRoadmapAtomic.first IntegralMixedRoadmapAtomic.point
 IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalMarkedPlan.bank
 IntegralMixedFramedHistoryFamilyBits.family

theorem midpoint_free (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (i : Fin (ambient hn ht ha hR0 q+1)) (hi : IntegralMixedRoadmapAtomic.depth q ≤ i.val) :
    midpoint hn ht ha hR0 q hv i=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.midProducer (D q) (N q) q i.val) :=by
  have H:=IntegralMixedRoadmapProper.midpointPoint_free hn ht ha hR0 q hv HB.1 HB.2.2.1
    (Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) i)
    (by have HD:=HB.1;simp only [Fin.val_cast];unfold IntegralMixedRoadmapProper.levelIndex;omega)
  simpa only [midpoint,field,Fin.val_cast] using H

theorem child_free (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (i : Fin (ambient hn ht ha hR0 q+1)) (hi : IntegralMixedRoadmapAtomic.depth q ≤ i.val) :
    child hn ht ha hR0 q hv i=
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.childProducer (D q) (N q) q i.val) :=by
  let j:=Fin.cast (congrArg (·+1) (ambient_eq hn ht ha hR0 q)) i
  have H:=IntegralMixedRoadmapIdentity.signature_point hn ht ha hR0 q hv j
  have HL:=IntegralMixedChronologicalPointSignatureCode.code_lookup (D q)
    (IntegralMixedRoadmapAtomic.first (D q) (N q) q) (IntegralMixedRoadmapAtomic.frozen q) j
  change Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapIdentity.ownSignature hn ht ha hR0 q) j.val)=_ at HL
  rw [HL] at H
  have HE : IntegralMixedChronologicalPointSignatureCode.producer (D q)
      (IntegralMixedRoadmapAtomic.first (D q) (N q) q) (IntegralMixedRoadmapAtomic.frozen q) j.val=
      IntegralMixedRoadmapProper.childProducer (D q) (N q) q i.val :=by
    unfold IntegralMixedChronologicalPointSignatureCode.producer
    rw [IntegralMixedRoadmapAtomic.frozen_count,ite_eq_right (by simpa only [j,Fin.val_cast] using Nat.not_lt.mpr hi)]
    unfold IntegralMixedRoadmapProper.childProducer
    have HJ:=j.isLt
    simp only [j,Fin.val_cast] at HJ ⊢
    omega
  rw [HE] at H
  simpa only [child,field,j] using H.symm

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
