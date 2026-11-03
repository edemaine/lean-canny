/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardOrigin
public import LeanCanny.Geometry.IntegralMixedFramedCriticalReadback
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Algebra.IntegralMixedCriticalRoot
/-! # Active critical creators and the literal geometric selected coordinate

The native correlation guard compares a retained bank quotient with the
powered ambient coordinate of its actual creating block. This identifies
the coordinate of that geometric point, not an arbitrary annihilator root.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedCriticalAnchor
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan family commands prefixLength defaultInstruction)
open IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedCriticalGuardBits
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool)
  (ha : Active P T key stage q)

theorem creating_chosen :
    chosen (commands P D (key q)) ⟨age P key stage q,age_lt P D H T key stage q ha⟩=
      IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q) :=by
  have HE : prefixLength P (key q)-1-age P key stage q=stage q:=by
    have HH:=ha.1
    unfold age
    omega
  exact (IntegralMixedFramedHistoryFamilyBits.origin_instruction P D H (key q)
    ⟨age P key stage q,age_lt P D H T key stage q ha⟩).trans (by rw [HE];rfl)

include H ha in
theorem creating_decomposition :
    commands P D (key q)=(commands P D (key q)).take (age P key stage q)++
      IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)::
      paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q) :=by
  let i : Fin (commands P D (key q)).length:=⟨age P key stage q,age_lt P D H T key stage q ha⟩
  have HE : prefixLength P (key q)-1-age P key stage q=stage q:=by
    have HH:=ha.1
    unfold age
    omega
  have HO:=paddedPast_older (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q)))
    (prefixLength P (key q)) i
  rw [HE] at HO
  change older (commands P D (key q)) i=paddedPast (defaultInstruction P D (pairFst (key q)))
    (D.rules (pairFst (key q))) (stage q) at HO
  have HT:=List.take_append_drop i.val (commands P D (key q))
  rw [List.drop_eq_getElem_cons i.isLt] at HT
  change (commands P D (key q)).take i.val++chosen (commands P D (key q)) i::older (commands P D (key q)) i=_ at HT
  rw [creating_chosen P D H T key stage q ha,HO] at HT
  exact HT.symm

private theorem instruction_critical {n B : ℕ} (c : Instruction n B) (r : CriticalRule n)
    (hc : c.command=.critical r) : c=⟨c.source,c.source_cap,.critical r⟩ :=by
  cases c with
  | mk Q hQ command => exact congrArg (fun cmd=>Instruction.mk Q hQ cmd) hc

include hr ha in
theorem exists_active_decomposition :
    ∃r : CriticalRule (P.ambient (pairFst (key q))),
      (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command=.critical r ∧
      commands P D (key q)=(commands P D (key q)).take (age P key stage q)++
        ⟨(IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).source,
          (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).source_cap,.critical r⟩::
        paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q) :=by
  obtain ⟨r,hc⟩:=active_critical P D H T hr key stage q ha
  refine ⟨r,hc,?_⟩
  exact (creating_decomposition P D H T key stage q ha).trans
    (congrArg (fun c=>(commands P D (key q)).take (age P key stage q)++c::
      paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q))
      (instruction_critical _ r hc))

noncomputable def geometricPoint (z : ℕ→ℝ) (i : Fin (P.ambient (pairFst (key q))+1)) : ℝ :=
  z (arity (paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q))+i.val)^
    physicalPower P key stage q

theorem geometricPoint_eq (z : ℕ→ℝ) :
    IntegralMixedFramedCriticalReadback.point (S:=P.cap (pairFst (key q))+1)
      (paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q)) z=
        geometricPoint P D key stage q z :=by
  funext i
  unfold IntegralMixedFramedCriticalReadback.point geometricPoint
  rw [paddedPast_length]
  rfl

include hr in
theorem zero_iff_selected_coordinate (r : CriticalRule (P.ambient (pairFst (key q))))
    (hc : (IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)).command=.critical r)
    (z : Fin (count P T key q)→ℝ) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) z=0↔
      IntegralMixedFramedCriticalGuard.actualPoint P D H T hr key stage q ha z=
        geometricPoint P D key stage q (IntegralMixedFramedBankObservation.extend z)
          (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
            (IntegralMixedCriticalRoot.coordinate r)) :=by
  have HE : geometricPoint P D key stage q (IntegralMixedFramedBankObservation.extend z)
      (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
        (IntegralMixedCriticalRoot.coordinate r))=
      z ⟨physical P T key stage q,physical_lt P D H T hr key stage q ha⟩^physicalPower P key stage q :=by
    unfold geometricPoint
    have HC:=physical_at_critical P D H T hr key stage q r hc
    change physical P T key stage q=_ at HC
    rw [show arity (paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q))+
      (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
        (IntegralMixedCriticalRoot.coordinate r)).val=physical P T key stage q from by
        simpa only [ClearedCoordinateCritical.freeIndex,IntegralMixedCriticalRoot.coordinate,Nat.add_assoc] using HC.symm]
    unfold IntegralMixedFramedBankObservation.extend
    rw [dite_eq_left (physical_lt P D H T hr key stage q ha)]
  exact (IntegralMixedFramedCriticalGuard.zero_iff_actualPoint P D H T hr key stage q ha z).trans
    (congrArg (fun a=>IntegralMixedFramedCriticalGuard.actualPoint P D H T hr key stage q ha z=a) HE.symm).to_iff

end LeanCanny.Geometry.IntegralMixedFramedCriticalAnchor
