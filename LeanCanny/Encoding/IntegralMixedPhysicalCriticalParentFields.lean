/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalLanguageCorrectness
/-! # Every interpreted critical-parent value is its actual full-child field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
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
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem parentValues_point (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (i : Fin ((G).birth (key n false false q))) :
    IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha hR false q hp i=
      IntegralMixedPhysicalCriticalBankEquality.point hn ht ha hR false false q
        (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i.val :=by
  have hi : i.val<birth n false false q:=i.isLt.trans_eq
    (IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false q)
  unfold IntegralMixedPhysicalCriticalInterval.parentValues IntegralMixedPhysicalCriticalInterval.parentArray
  rw [IntegralFramedPhysicalSquare.bank_naturalPoint]
  unfold IntegralMixedPhysicalCriticalBankEquality.point
  apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
    (key n false false) (positive hn ht ha hR false false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
  apply Fin.ext
  symm
  simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using
    IntegralMixedPhysicalCriticalBankEquality.coordinate_val hn ht ha hR false false q i.val 0 hi

theorem parentValues_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR false (pair q w))
    (i : Fin ((G).birth (key n false false q))) :
    IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha hR false q hp i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha hR (context q) w hc
        (birth n false false q-1-i.val) :=by
  have hi : i.val<birth n false false q:=i.isLt.trans_eq
    (IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false q)
  have HE:=parent_point_field hn ht ha hR q w hp hv hc hg i.val hi
  have HC : IntegralMixedPhysicalFieldEquality.count hn ht ha hR (context q)=birth n false false q+1:=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq hn ht ha hR]
    have HF:=full_birth (n:=n) q
    have HS:=IntegralMixedPhysicalCriticalPrefixes.consecutive n false q
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
    omega
  have HX : IntegralMixedPhysicalFieldEquality.newest
      (IntegralMixedPhysicalFieldEquality.count hn ht ha hR (context q)) (birth n false false q-1-i.val)=i.val+1:=by
    rw [HC]
    unfold IntegralMixedPhysicalFieldEquality.newest
    rw [min_eq_left (by omega : birth n false false q-1-i.val≤birth n false false q+1-1)]
    omega
  exact (parentValues_point hn ht ha hR q hp i).trans
    (HE.trans (by rw [IntegralMixedPhysicalFieldEquality.point,HX]))

theorem endpoint_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR false (pair q w))
    (j : ℕ) (hj : j<birth n false false q) :
    IntegralMixedPhysicalCriticalInterval.endpointValue hn ht ha hR false q hp j=
      IntegralMixedPhysicalFieldEquality.point hn ht ha hR (context q) w hc j :=by
  have hi : birth n false false q-1-j<(G).birth (key n false false q):=by
    rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false]
    omega
  have HE:=parentValues_field hn ht ha hR q w hp hv hc hg ⟨birth n false false q-1-j,hi⟩
  have HX : birth n false false q-1-(birth n false false q-1-j)=j:=by omega
  rw [HX] at HE
  exact (parentValues_point hn ht ha hR q hp ⟨birth n false false q-1-j,hi⟩).symm.trans HE

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
