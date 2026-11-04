/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProducerBounds
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedMidpoint
/-! # Every genuine free-coordinate query of an accepted proper level is well formed -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  creating IntegralMixedRoadmapAtomic.depth

theorem row_good_of_valid (q :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd :0<IntegralMixedRoadmapAtomic.depth q) (j :ℕ)
    (hj :IntegralMixedRoadmapAtomic.depth q≤j) (hjn :j≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):
    IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (pair q (BinaryNatCode.encode j)):=by
  have HM:=IntegralMixedRoadmapProper.checked_midpoint_good
    (IntegralMixedRoadmapAtomic.checked hn ht ha hR0 q hv) hd
  have HFit:=IntegralMixedRoadmapProper.mid_producer_before_probe hn ht ha hR0 q hv hd j hj hjn
  have HBirth :IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q≤creating hn ht ha hR0 (pair q (BinaryNatCode.encode j)):=by
    unfold IntegralMixedRoadmapProper.midProducer IntegralMixedRoadmapProper.midFirst at HFit
    omega
  rcases HM with ⟨HL,HA,HB,HLo,HUp,_,_⟩
  have HG :IntegralMixedChronologicalFrameCode.Good
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (creating hn ht ha hR0 (pair q (BinaryNatCode.encode j))) (IntegralMixedRoadmapProper.labels q):=
    ⟨HL.1,fun i hi=>(HL.2 i hi).trans_le HBirth⟩
  have HK:=IntegralMixedRoadmapProper.labels_count q
  unfold IntegralMixedRoadmapProperRowWitness.RowGood
  simp only [dimension,atomic,labels,oldProducer,offset,coordinate,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]
  refine ⟨⟨HG,HLo,HUp,?_,by omega⟩,HG,HA.trans_le HBirth,HB.trans_le HBirth,HLo,HUp,?_,by omega⟩ <;>
    unfold IntegralMixedRoadmapProper.levelIndex at * <;> omega

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
