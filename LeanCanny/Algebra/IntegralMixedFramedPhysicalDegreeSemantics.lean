/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowDegree

/-! # Literal physical degree branches and their old-column transport -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeSemantics
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript (Instruction Index run)
open IntegralMixedFramedPhysicalIndex (arity enumerate block criticalEquiv)
open IntegralMixedFramedPhysicalPersistence
open IntegralMixedFramedPhysicalRowDegree
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def values {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction n B)) (hc : cs.length≤S+1) (j : ℕ) :=
  if hj : j<arity cs then (run initial cs hc).sampler.degrees ((enumerate cs).symm ⟨j,hj⟩) else 1

theorem values_append {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (newer older : List (Instruction n B))
    (h : (newer++older).length≤S+1) (ho : older.length≤S+1) (j : ℕ) (hj : j<arity older) :
    values initial (newer++older) h j=values initial older ho j := by
  have HJ : j<arity (newer++older):=hj.trans_le (arity_le_append newer older)
  simp only [values,dite_eq_left HJ,dite_eq_left hj]
  exact run_indexed_degrees initial newer older h ho ⟨j,hj⟩

def blockDegree (n D offset S B m : ℕ) (critical : Bool) (j : ℕ) :=
  if j=(if critical then block n else 0) then 2^B*birth S (2^B) m
  else if j=n+1 then D*physical S (2^B) m
  else if n+2≤j ∧ j-(n+2)<offset then physical S (2^B) m
  else (D-1)*physical S (2^B) m

theorem critical_block_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n)
    (j : FlatAffineCriticalStage.Variables (n+1)) :
    (IntegralMixedHistory.criticalStep x hm r).sampler.degrees (Sum.inl (Sum.inr j))=
      blockDegree n P.degree r.offset.val S B m true (criticalEquiv j).val := by
  cases j with
  | inl i=>
    rw [critical_ambient_degree]
    change _=blockDegree n P.degree r.offset.val S B m true i.val
    have HS : i.val≠block n:=by have HI:=i.isLt; unfold block; omega
    have HN : i.val≠n+1:=Nat.ne_of_lt i.isLt
    have HF : ¬ (n + 2 ≤ i.val ∧ i.val - (n + 2) < r.offset.val):=by have HI:=i.isLt; omega
    simp only [blockDegree,ite_true,ite_eq_right HS,ite_eq_right HN,ite_eq_right HF]
  | inr k=>
    refine Fin.cases ?_ (fun i=>?_) k
    · rw [critical_source_degree]
      change _=blockDegree n P.degree r.offset.val S B m true (n+1+0)
      have HS : n+1≠block n:=by unfold block; omega
      simp only [Nat.add_zero,blockDegree,ite_true,ite_eq_right HS,ite_true]
    · rw [critical_height_degree]
      change _=blockDegree n P.degree r.offset.val S B m true (n+1+(i.val+1))
      have HS : n+1+(i.val+1)≠block n:=by have HI:=i.isLt; unfold block; omega
      have HN : n+1+(i.val+1)≠n+1:=by omega
      have HF : (n+2≤n+1+(i.val+1) ∧ (n+1+(i.val+1))-(n+2)<r.offset.val)↔i.val<r.offset.val:=by omega
      simp only [blockDegree,ite_true,ite_eq_right HS,ite_eq_right HN,HF]

theorem critical_equiv_column {n B a : ℕ} {P : SpatialSource n} {ι : Type}
    (r : CriticalRule n) (e : ι≃Fin a) (j : FlatAffineCriticalStage.Variables (n+1)) :
    (IntegralMixedFramedPhysicalIndex.stepEquiv (.critical (P:=P) (B:=B) r) e (Sum.inl (Sum.inr j))).val=
      a+(criticalEquiv j).val := by
  cases j <;> rfl


theorem fresh_column_local {n B a : ℕ} {P : SpatialSource n} {ι : Type}
    (c : IntegralMixedFullHistoryScript.Command P B) (e : ι≃Fin a) :
    (IntegralMixedFramedPhysicalIndex.stepEquiv c e (IntegralMixedFramedPhysicalIndex.fresh c)).val-a=
      IntegralMixedFramedPhysicalIndex.added c-1 := by
  rw [IntegralMixedFramedPhysicalIndex.step_fresh]
  cases c <;> simp only [IntegralMixedFramedPhysicalIndex.added,
    IntegralMixedFullHistoryScript.Command.isCritical,ite_true,ite_false,Bool.false_eq_true]
  all_goals omega

theorem fresh_block_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.degrees (IntegralMixedFramedPhysicalIndex.fresh c)=
      blockDegree n P.degree (IntegralMixedCommandHeaderBits.command c).offset S B m c.isCritical
        (IntegralMixedFramedPhysicalIndex.added c-1) := by
  rw [fresh_scalar_degree]
  cases c <;> simp only [blockDegree,IntegralMixedFramedPhysicalIndex.added,
    IntegralMixedFullHistoryScript.Command.isCritical,ite_true,ite_false,Bool.false_eq_true,
    Nat.add_sub_cancel,Nat.sub_self]

theorem step_fresh_degree {n S B m a : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B) (e : ι≃Fin a) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.degrees (IntegralMixedFramedPhysicalIndex.fresh c)=
      blockDegree n P.degree (IntegralMixedCommandHeaderBits.command c).offset S B m c.isCritical
        ((IntegralMixedFramedPhysicalIndex.stepEquiv c e (IntegralMixedFramedPhysicalIndex.fresh c)).val-a) :=
  (fresh_block_degree x hm c).trans (congrArg
    (blockDegree n P.degree (IntegralMixedCommandHeaderBits.command c).offset S B m c.isCritical)
    (fresh_column_local c e).symm)

theorem step_new_degree {n S B m a : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m≤S) (c : IntegralMixedFullHistoryScript.Command P B)
    (e : ι≃Fin a) (i : IntegralMixedFullHistoryScript.NextIndex ι c)
    (hi : a≤(IntegralMixedFramedPhysicalIndex.stepEquiv c e i).val) :
    (IntegralMixedFullHistoryScript.step x hm c).sampler.degrees i=
      blockDegree n P.degree (IntegralMixedCommandHeaderBits.command c).offset S B m c.isCritical
        ((IntegralMixedFramedPhysicalIndex.stepEquiv c e i).val-a) := by
  cases c with
  | integer p hp hd=>
    cases i with
    | inl j=>have HJ:=(e j).isLt; change a≤(e j).val at hi; omega
    | inr u=>
      cases u
      exact step_fresh_degree x hm (.integer p hp hd) e
  | critical r=>
    cases i with
    | inl j=>
      cases j with
      | inl j=>have HJ:=(e j).isLt; change a≤(e j).val at hi; omega
      | inr j=>
        rw [critical_equiv_column,Nat.add_sub_cancel_left]
        exact critical_block_degree x hm r j
    | inr u=>
      cases u
      exact step_fresh_degree x hm (.critical r) e
  | cut r k d hs hd=>
    cases i with
    | inl j=>have HJ:=(e j).isLt; change a≤(e j).val at hi; omega
    | inr u=>
      cases u
      exact step_fresh_degree x hm (.cut r k d hs hd) e

end LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeSemantics
