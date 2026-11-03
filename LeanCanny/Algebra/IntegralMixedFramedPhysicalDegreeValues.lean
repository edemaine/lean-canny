/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeSemantics
public import LeanCanny.Algebra.IntegralMixedFramedHistoryPrefix

/-! # Natural row-degree profiles restrict to their actual creating prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeValues
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript (Instruction Index run paddedPast paddedPast_length)
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open IntegralMixedFramedPhysicalPersistence
open IntegralMixedFramedPhysicalDegreeSemantics
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem values_congr {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) (r : ℕ) :
    values initial cs hc r=values initial ds hd r := by
  cases he
  rfl

theorem values_cons_new {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (c : Instruction n B) (cs : List (Instruction n B))
    (h : (c::cs).length≤S+1) (r : ℕ) (hl : arity cs≤r) (hu : r<arity (c::cs)) :
    values initial (c::cs) h r=
      blockDegree n c.source.degree (IntegralMixedCommandHeaderBits.command c.command).offset
        S B cs.length c.command.isCritical (r-arity cs) := by
  have HC : cs.length≤S+1 :=by simp only [List.length_cons] at h; omega
  have HM : cs.length≤S :=by simp only [List.length_cons] at h; omega
  let x:=reframe (run initial cs HC) c.source c.source_cap
  let j:=((enumerate (c::cs)).symm ⟨r,hu⟩)
  have HE : (IntegralMixedFramedPhysicalIndex.stepEquiv c.command (enumerate cs) j).val=r :=
    congrArg Fin.val ((enumerate (c::cs)).apply_symm_apply ⟨r,hu⟩)
  have HJ : arity cs≤(IntegralMixedFramedPhysicalIndex.stepEquiv c.command (enumerate cs) j).val :=by
    rw [HE]
    exact hl
  have H:=step_new_degree x HM c.command (enumerate cs) j HJ
  unfold values
  rw [dite_eq_left hu]
  exact H.trans (congrArg
    (blockDegree n c.source.degree (IntegralMixedCommandHeaderBits.command c.command).offset S B cs.length c.command.isCritical)
    (congrArg (fun k : ℕ=>k-arity cs) HE))

theorem padded_split {n B : ℕ} (fallback : Instruction n B) (cs : List (Instruction n B))
    (m b : ℕ) (hb : b≤m) :
    paddedPast fallback cs m=
      (paddedPast fallback cs m).take (m-b)++paddedPast fallback cs b := by
  have H:=List.take_append_drop (m-b) (paddedPast fallback cs m)
  rw [IntegralMixedFramedHistoryScript.paddedPast_drop fallback cs m b hb] at H
  exact H.symm

theorem values_padded_older {n S B : ℕ} {P : SpatialSource n}
    (initial : State P S B 0 (Fin 0)) (fallback : Instruction n B) (cs : List (Instruction n B))
    (m b : ℕ) (hm : m≤S+1) (hb : b≤m) (r : ℕ) (hr : r<arity (paddedPast fallback cs b)) :
    values initial (paddedPast fallback cs m) (by rw [paddedPast_length]; exact hm) r=
      values initial (paddedPast fallback cs b) (by rw [paddedPast_length]; exact hb.trans hm) r := by
  let newer:=(paddedPast fallback cs m).take (m-b)
  have HE:=padded_split fallback cs m b hb
  have HC : (newer++paddedPast fallback cs b).length≤S+1 := by
    rw [←HE,paddedPast_length]
    exact hm
  exact (values_congr initial _ _ HE _ HC r).trans
    (values_append initial newer (paddedPast fallback cs b) HC _ r hr)

end LeanCanny.Algebra.IntegralMixedFramedPhysicalDegreeValues
