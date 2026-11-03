/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.IntegralMixedCutRecordModuloDegree
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
/-! # Every accepted ordinary hint has the actual typed current-Q probe shape -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedRoadmapBadProbePacket IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem raw_good (n initial B : ℕ) (z : List Bool) (h : HintGood n initial B z) :
    IntegralMixedChronologicalCutCode.Good n (creating initial (pairFst z)) (labels (pairFst z))
      (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)):=by
 refine ⟨h.2.1,le_refl _,?_,h.2.2.2.1,h.2.2.2.2.1⟩
 exact lt_of_le_of_lt h.2.2.2.1 h.2.2.2.2.1

theorem tag_le (n initial B : ℕ) (z : List Bool) (h : HintGood n initial B z) :
    Nat.fromBitsLE (field 0 z)≤2:=by have H:=h.2.2.1;omega

noncomputable def data (n initial B : ℕ) (z : List Bool) (h : HintGood n initial B z) :=
 IntegralMixedChronologicalCutCode.rawData n (creating initial (pairFst z)) (labels (pairFst z))
   (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)) (raw_good n initial B z h)

theorem probe_eq (n initial B : ℕ) (z : List Bool) (h : HintGood n initial B z) :
    probe n z=(data n initial B z h).code
      (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
      (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z)):=
 (IntegralMixedChronologicalCutCode.rawData_code n (creating initial (pairFst z)) (labels (pairFst z))
   _ _ (raw_good n initial B z h) _ _ _ (tag_le n initial B z h)).symm

theorem command {n S B : ℕ} (P : SpatialSource n) (hn : 0<n) (initial : ℕ) (z : List Bool)
    (h : HintGood n initial B z) {ι : Type}
    (x : State P S B (creating initial (pairFst z)) ι)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (IntegralMixedCausalUnitRecordBits.record P hn (creating initial (pairFst z)) (probe n z) hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=
      .cut ((data n initial B z h).rule (commonDenominator x) (commonDenominator_ne_zero x))
        (((data n initial B z h).cut P (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
          (Nat.fromBitsLE (field 2 z)) (IntegralMixedCutRecordConstructor.degreeResidue P (Nat.fromBitsLE (field 3 z)))
          (IntegralMixedCutRecordConstructor.degreeResidue_le P _) hcap).kind
            (commonDenominator x) (commonDenominator_ne_zero x))
        (IntegralMixedCutRecordConstructor.degreeResidue P (Nat.fromBitsLE (field 3 z)))
        (IntegralMixedCutRecordConstructor.degreeResidue_le P _) ((IntegralMixedCutRecordConstructor.degreeResidue_le P _).trans hcap):=by
 rw [probe_eq n initial B z h]
 exact IntegralMixedCutRecordConstructor.command_decode_mod _ P hn _ _ _ hcap _ _

theorem kind_ordinary {n B : ℕ} (P : SpatialSource n) (initial : ℕ) (z : List Bool)
    (h : HintGood n initial B z) (Q : ℤ) (hQ : Q≠0)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    IntegralMixedSelectedBadMembership.Ordinary ((data n initial B z h).rule Q hQ)
      (((data n initial B z h).cut P (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
        (Nat.fromBitsLE (field 2 z)) (IntegralMixedCutRecordConstructor.degreeResidue P (Nat.fromBitsLE (field 3 z)))
        (IntegralMixedCutRecordConstructor.degreeResidue_le P _) hcap).kind Q hQ):=by
 have HT:=tag_le n initial B z h
 generalize HE : Nat.fromBitsLE (field 0 z)=tag at HT ⊢
 interval_cases tag
 · change (0:ℕ)<3
   decide
 · change (1:ℕ)<3
   decide
 · change (2:ℕ)<3
   decide

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape
