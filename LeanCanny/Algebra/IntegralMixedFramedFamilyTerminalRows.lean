/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
public import LeanCanny.Algebra.IntegralMixedFramedTerminalPrefix

/-! # Literal joint prefix rows after the first default birth

The saved family may use a different spatial source from its terminal run.
Reframing leaves its scalar rows unchanged. The extra prefix birth is the
existing default integer X, with no extra encoded instruction.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

private theorem run_rows_congr {n S B : ℕ} {Q : SpatialSource n}
    (initial : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    HEq (run initial cs hc).sampler.scalarPrefix.rows
      (run initial ds hd).sampler.scalarPrefix.rows := by
  cases he
  rfl

private theorem runAt_rows_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hi : i=j) (hc : i≤P.cap r+1) (hd : j≤P.cap s+1) :
    HEq (runAt P D r i hc).sampler.scalarPrefix.rows
      (runAt P D s j hd).sampler.scalarPrefix.rows := by
  cases hr
  cases hi
  rfl

private theorem terminal_rows (P : Parameters) (D : Plan P) (root : List Bool)
    (hm : (D.rules root).length≤P.cap root) :
    HEq (runAt P D root ((D.rules root).length+1) (Nat.succ_le_succ hm)).sampler.scalarPrefix.rows
      (run (IntegralMixedFramedHistoryFamilyBits.initial P D root)
        (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root)
        (by simp only [List.length_cons]; omega)).sampler.scalarPrefix.rows :=
  run_rows_congr (IntegralMixedFramedHistoryFamilyBits.initial P D root) _ _
    (paddedPast_after _ _) _ _

theorem family_terminal_rows (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (root context : List Bool)
    (hm : (D.rules root).length≤P.cap root) :
    HEq (((IntegralMixedFramedHistoryFamilyBits.family P D H).state
      (IntegralMixedFramedHistoryFamilyBits.keyAt root ((D.rules root).length+1) context)).sampler.scalarPrefix.rows)
      (run (IntegralMixedFramedHistoryFamilyBits.initial P D root)
        (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root::D.rules root)
        (by simp only [List.length_cons]; omega)).sampler.scalarPrefix.rows := by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root ((D.rules root).length+1) context
  have H1 : HEq (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.rows)
      (runAt P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)
        (min_le_right _ _)).sampler.scalarPrefix.rows := HEq.rfl
  exact H1.trans ((runAt_rows_congr P D _ root _ _ (pairFst_pair _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ context (Nat.succ_le_succ hm))
    (min_le_right _ _) (Nat.succ_le_succ hm)).trans (terminal_rows P D root hm))

end LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
