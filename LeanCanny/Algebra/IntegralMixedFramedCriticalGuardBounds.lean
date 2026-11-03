/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardQueries
/-! # Actual original critical headers select valid full physical columns -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool)

include hr in
theorem count_actual : count P T key q=arity (commands P D (key q)) :=
  prefixArity_packet P D H T hr (key q) _

theorem age_lt (ha : Active P T key stage q) : age P key stage q<(family P D H).birth (key q) := by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
  have HM:=ha.1
  unfold age
  omega

include hr in
theorem scalar_lt (ha : Active P T key stage q) : scalar P T key stage q<count P T key q := by
  have HL : (commands P D (key q)).length=IntegralMixedFramedHistoryFamilyBits.prefixLength P (key q) :=
    IntegralMixedFramedHistoryScript.paddedPast_length _ _ _
  let i : Fin (commands P D (key q)).length:=⟨age P key stage q,by
    rw [HL]
    exact (age_lt P D H T key stage q ha).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth _ _ _ _)⟩
  change scalarColumn P T (pair (key q) (BinaryNatCode.encode (age P key stage q)))<count P T key q
  rw [count_actual P D H T hr key q,scalarColumn_packet P D H T hr _ _ (i.isLt.trans_eq HL)]
  exact (enumerate_scalar (commands P D (key q)) i).symm.trans_lt (enumerate _ _).isLt

private theorem critical_coordinate_bound {n B : ℕ} {S : IntegralMixedHistory.SpatialSource n}
    (c : IntegralMixedFullHistoryScript.Command S B) (hc : (IntegralMixedCommandHeaderBits.command c).context=1) :
    (IntegralMixedCommandHeaderBits.command c).offset+(IntegralMixedCommandHeaderBits.command c).coordinate<n+1 := by
  cases c with
  | integer=>exact False.elim (by cases hc)
  | critical r=>
    change r.offset.val+r.coordinate%(n-r.offset.val+1)<n+1
    have HM:=Nat.mod_lt r.coordinate (by have HO:=r.offset.isLt; omega : 0<n-r.offset.val+1)
    have HO:=r.offset.isLt
    omega
  | cut r k=>cases k <;> cases hc

include hr in
theorem physical_lt (ha : Active P T key stage q) : physical P T key stage q<count P T key q := by
  let K:=key q
  let j:=stage q
  let m:=IntegralMixedFramedHistoryFamilyBits.prefixLength P K
  have Hcoord : (header T key stage q).offset+(header T key stage q).coordinate<P.ambient (pairFst K)+1 := by
    have HH:=IntegralMixedFramedHeaderBits.lookup_words (D.rules (pairFst K))
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst K)) (by rfl) j
    have HH' : header T key stage q=IntegralMixedCommandHeaderBits.command
      ((IntegralMixedFramedHistoryScript.chronological (D.rules (pairFst K)) j).getD
        (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst K))).command := by
      unfold header
      rw [hr.commands]
      exact HH
    rw [HH']
    exact critical_coordinate_bound _ (HH'.symm ▸ ha.2)
  have Hspan : span P T (pair K (List.replicate j true))=block (P.ambient (pairFst K))+1 := by
    unfold span
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
    exact ite_eq_left ha.2
  have HS : prefixArity P T (pair K (List.replicate (j+1) true))=
      prefixArity P T (pair K (List.replicate j true))+block (P.ambient (pairFst K))+1 := by
    simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate,Finset.sum_range_succ]
    rw [Hspan]
    omega
  have Hle : prefixArity P T (pair K (List.replicate (j+1) true))≤prefixArity P T (pair K (List.replicate m true)) := by
    simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_of_lt ha.1))
  unfold physical count packet
  change prefixArity P T (pair K (List.replicate j true))+(header T key stage q).offset+
    (header T key stage q).coordinate<prefixArity P T (pair K (List.replicate m true))
  unfold block at HS
  omega
end LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBits
