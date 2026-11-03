/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRetarget
/-! # Actual original current-Q rules from a checked literal ordinary cut code -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H

private theorem raw_rule_birth {a b N : ℕ} (labels : List Bool) (g j : ℕ)
    (ha : IntegralMixedChronologicalCutCode.Good N a labels g j)
    (hb : IntegralMixedChronologicalCutCode.Good N b labels g j) (he : a=b) (Q : ℤ) (hQ : Q≠0) :
    (IntegralMixedChronologicalCutCode.rawData N a labels g j ha).rule Q hQ=
      (IntegralMixedChronologicalCutCode.rawData N b labels g j hb).rule Q hQ:=by
 cases he
 rfl

variable (key : List Bool) (codes : List (List Bool)) (labels : List Bool) (g j tag choice degree : ℕ)
 (hgood : IntegralMixedChronologicalCutCode.Good
   ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient (pairFst key))
   (number n (pairFst key)+8+codes.length) labels g j)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
   (codes++[IntegralMixedChronologicalCutCode.code
     ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient (pairFst key)) labels g j tag choice degree]))
 (hk : prefixLength (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters key=number n (pairFst key)+8+codes.length)

include hgood htable hk in
theorem ordinary_raw (htag : tag≤2) :
    IntegralMixedSelectedBadMembership.Ordinary ((G).rule key) ((G).kind key):=by
 let d:=IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst key))
   (number n (pairFst key)+8+codes.length) labels g j hgood
 have HC :IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
     (codes++[d.code (IntegralMixedChronologicalCutCode.ordinaryTag tag) choice degree]):=by
   rw [IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ hgood tag choice degree htag]
   exact htable
 exact ordinary hn ht ha hR0 key codes d (IntegralMixedChronologicalCutCode.ordinaryTag tag) choice degree HC hk
   (by rw [IntegralMixedChronologicalCutCode.ordinaryTag_index tag htag];omega)

include hgood htable hk in
theorem rule_raw (htag : tag≤2) :
    ∃h : IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst key)) ((G).birth key) labels g j,
    (G).rule key=(IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst key)) ((G).birth key)
      labels g j h).rule (commonDenominator ((G).state key)) (commonDenominator_ne_zero ((G).state key)):=by
 let d:=IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst key))
   (number n (pairFst key)+8+codes.length) labels g j hgood
 have HC :IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
     (codes++[d.code (IntegralMixedChronologicalCutCode.ordinaryTag tag) choice degree]):=by
   rw [IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ hgood tag choice degree htag]
   exact htable
 have HB : (G).birth key=number n (pairFst key)+8+codes.length:=
   (IntegralMixedFramedHistoryFamilyBits.family_birth P (B).plan (B).data key).trans hk
 have HG :IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst key)) ((G).birth key) labels g j:=HB.symm ▸ hgood
 refine ⟨HG,?_⟩
 exact (rule_eq hn ht ha hR0 key codes d (IntegralMixedChronologicalCutCode.ordinaryTag tag) choice degree HC hk).trans
   (raw_rule_birth labels g j hgood HG HB.symm _ _)

end LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
