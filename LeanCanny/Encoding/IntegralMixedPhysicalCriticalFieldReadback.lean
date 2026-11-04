/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
/-! # The parent-child scan identifies literal chronological full-word fields -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open IntegralMixedPhysicalCriticalPrefixes (key input positive birth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem child_point_field (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (i : ℕ) (hi : i<birth n false false q) :
    IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR false true q w hv i=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR (context q) w hc (i+1) :=by
  let z:=IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs
    (key n false true) (positive hn ht ha hR false true) q w hv
  have HN:=natural_full hn ht ha hR q w hv hc
  have HR : pairFst (key n false true q)=pairFst ((B).key (context q)):=by
    rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha hR]
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,context,pairFst_pair]
  have HB : prefixLength P (key n false true q)=prefixLength P ((B).key (context q)):=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,
      ←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,
      IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false true]
    change birth n false true q=IntegralMixedPhysicalFieldEquality.count hn ht ha hR (context q)
    rw [full_birth,IntegralMixedPhysicalFieldEquality.count_eq hn ht ha hR]
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HO:=IntegralMixedFullBankObservation.point_sibling P D H H (key n false true q)
    ((B).key (context q)) HR HB z (i+1)
  have HP:=IntegralMixedPhysicalCriticalInterval.bank_point_observation hn ht ha hR false true q w hv z
    (fun j=>(IntegralFramedPhysicalSquare.naturalPoint_at P D H L F C hs
      (key n false true) (positive hn ht ha hR false true) q w hv j).symm) i hi
  have HC : i+1<IntegralMixedPhysicalFieldEquality.count hn ht ha hR (context q):=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq hn ht ha hR]
    have HF:=full_birth (n:=n) q
    have HS:=IntegralMixedPhysicalCriticalPrefixes.consecutive n false q
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
    omega
  have HE:=IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs (B).key (B).positive
    (context q) w hc ⟨i+1,HC⟩
  have HX : IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR (context q) w hc (i+1)=
      IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context q) w hc ⟨i+1,HC⟩:=by
    unfold IntegralMixedPhysicalFieldEquality.pointNewest
    apply congrArg (IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context q) w hc)
    apply Fin.ext
    exact min_eq_left (by omega)
  exact HP.trans (HO.trans ((congrArg (fun v=>
    (IntegralMixedFullBankObservation.atFamily P D H ((B).key (context q))).point v (i+1)) HN).trans
      (HE.trans HX.symm)))

theorem parent_point_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR false (pair q w))
    (i : ℕ) (hi : i<birth n false false q) :
    IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR false false q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR (context q) w hc (i+1) :=
  ((IntegralMixedPhysicalCriticalBankEquality.agrees_iff hn ht ha hR false q w hp hv).mp hg i hi).trans
    (child_point_field hn ht ha hR q w hv hc i hi)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
