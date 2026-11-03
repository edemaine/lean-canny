/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch
/-! # Fixed-width hint search covers every accepted ordinary probe

Canonicalizing the four numbers preserves the literal prepared root and
interval query. Only words at that SAME root are retained in this argument.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

private theorem dimension_hint (base hint : List Bool) :
    IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base hint)=
      IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base []) :=by
  simp only [IntegralMixedRoadmapBadProbeTest.dimension,pairFst_pair]
private theorem initial_hint (base hint : List Bool) :
    IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (pair base hint)=
      IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (pair base []) :=by
  simp only [IntegralMixedRoadmapBadProbeTest.initial,dimension_hint hn ht ha hR]
private theorem width_hint (base hint : List Bool) :
    IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base hint)=
      IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base []) :=by
  simp only [IntegralMixedRoadmapBadProbeTest.width,pairFst_pair]
attribute [local irreducible] IntegralMixedRoadmapBadProbeTest.dimension
  IntegralMixedRoadmapBadProbeTest.initial IntegralMixedRoadmapBadProbeTest.width

private theorem probe_hint_eq (d : ℕ) (base hL hR : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR))) :
    IntegralMixedRoadmapBadProbePacket.probe d (pair base hL)=
      IntegralMixedRoadmapBadProbePacket.probe d (pair base hR) :=by
  unfold IntegralMixedRoadmapBadProbePacket.probe
  simp only [pairFst_pair]
  rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]

private theorem prepared_hint_eq (d : ℕ) (base hL hR : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR))) :
    IntegralMixedRoadmapBadProbePacket.preparedRoot d (pair base hL)=
      IntegralMixedRoadmapBadProbePacket.preparedRoot d (pair base hR) :=by
  unfold IntegralMixedRoadmapBadProbePacket.preparedRoot IntegralMixedRoadmapBadProbePacket.preparedRaw
  simp only [pairFst_pair]
  rw [probe_hint_eq d base hL hR he]

theorem witness_hint_iff (base hL hR' w : List Bool)
    (he : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hL))=
      Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hR'))) :
    IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (pair base hL) w) ↔
      IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (pair base hR') w) :=by
  have HQ:=prepared_hint_eq (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base hL)) base hL hR' he
  simp only [dimension_hint hn ht ha hR] at HQ
  have HG : IntegralMixedRoadmapBadProbePacket.HintGood
      (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base hL))
      (IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (pair base hL))
      (IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base hL)) (pair base hL) ↔
    IntegralMixedRoadmapBadProbePacket.HintGood
      (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR (pair base hR'))
      (IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR (pair base hR'))
      (IntegralMixedRoadmapBadProbeTest.width hn ht ha hR (pair base hR')) (pair base hR') :=by
    unfold IntegralMixedRoadmapBadProbePacket.HintGood
    simp only [pairFst_pair,dimension_hint hn ht ha hR,initial_hint hn ht ha hR,width_hint hn ht ha hR]
    rw [he 0 (by decide),he 1 (by decide),he 2 (by decide),he 3 (by decide)]
  have HI : IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR (pair base hL)=
      IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR (pair base hR') :=by
    unfold IntegralMixedRoadmapBadProbeTest.intervalContext IntegralMixedRoadmapBadProbePacket.intervalContext
    simp only [pairFst_pair,dimension_hint hn ht ha hR,initial_hint hn ht ha hR]
    rw [HQ]
  have HF : IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR (pair (pair base hL) w)=
      IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR (pair (pair base hR') w) :=by
    unfold IntegralMixedRoadmapBadProbeTest.fieldPacket
    simp only [pairFst_pair,pairSnd_pair,dimension_hint hn ht ha hR,initial_hint hn ht ha hR]
    rw [HQ]
  simp only [IntegralMixedRoadmapBadProbeTest.Witness,pairFst_pair,pairSnd_pair,
    IntegralMixedRoadmapBadProbeTest.intervalPacket,HG,HI,HF]

theorem hasBadProbe_iff (base : List Bool) : HasBadProbe hn ht ha hR base ↔
    ∃hint : List Bool,IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hR (pair base hint) :=by
  constructor
  · rintro ⟨bits,_,h⟩
    refine ⟨pairSnd (hintPacket hn ht ha hR (pair base bits)),?_⟩
    simpa only [hintPacket,pairFst_pair,pairSnd_pair] using h
  · rintro ⟨hint,h⟩
    obtain ⟨w,HW⟩:=(IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha hR _).mp h
    let e : ℕ→ℕ:=fun i=>Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i (pair base hint))
    have HG:=HW.1
    simp only [pairFst_pair,dimension_hint hn ht ha hR,initial_hint hn ht ha hR,width_hint hn ht ha hR] at HG
    have Hfit:=ordinary_fields_fit hn ht ha hR base (e 0) (e 1) (e 2) (e 3)
      HG.2.2.1 HG.2.2.2.2.1 HG.2.2.2.2.2.1 HG.2.2.2.2.2.2.1
    have HE : ∀i<4,e i<2^blockWidth hn ht ha hR base:=by
      intro i hi
      interval_cases i
      · exact Hfit.1
      · exact Hfit.2.1
      · exact Hfit.2.2.1
      · exact Hfit.2.2.2
    let bits:=FixedWidthNatVector.encode 4 (blockWidth hn ht ha hR base) e
    have HEq : ∀i<4,Nat.fromBitsLE (IntegralMixedRoadmapBadProbePacket.field i
        (hintPacket hn ht ha hR (pair base bits)))=e i:=encode_fields hn ht ha hR base e HE
    refine ⟨bits,FixedWidthNatVector.length_encode _ _ _,?_⟩
    apply (IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha hR _).mpr
    refine ⟨w,?_⟩
    have HI:=witness_hint_iff hn ht ha hR base
      (pairSnd (hintPacket hn ht ha hR (pair base bits))) hint w (by
        intro i hi
        simpa only [hintPacket,pairFst_pair,pairSnd_pair] using HEq i hi)
    have Hnew:=HI.mpr HW
    simpa only [hintPacket,pairFst_pair,pairSnd_pair] using Hnew

theorem noBadProbe_iff (base : List Bool) : NoBadProbe hn ht ha hR base ↔
    ∀hint w : List Bool,¬IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (pair base hint) w) :=by
  rw [NoBadProbe,hasBadProbe_iff hn ht ha hR]
  simp only [IntegralMixedRoadmapBadProbeTest.hasWitness_iff hn ht ha hR,not_exists]

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch
