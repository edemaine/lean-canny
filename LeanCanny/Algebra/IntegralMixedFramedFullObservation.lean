/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Algebra.IntegralMixedFramedFamilyTerminalRows

/-! # The full saved prefix has the literal completed script's rows and bank data -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullObservation
open LeanCanny.Encoding IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt initial)
open IntegralMixedFramedBankObservation (ofState atRun)
open scoped Classical

private theorem run_rows_congr {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    HEq (run x cs hc).sampler.scalarPrefix.rows (run x ds hd).sampler.scalarPrefix.rows := by
  cases he
  rfl

private theorem rows_at_congr (P : Parameters) (D : Plan P) (r s : List Bool) (i j : ℕ)
    (hr : r=s) (hi : i=j) (hc : i≤P.cap r+1) (hd : j≤P.cap s+1) :
    HEq (IntegralMixedFramedFamilyRunView.runAt P D r i hc).sampler.scalarPrefix.rows
      (IntegralMixedFramedFamilyRunView.runAt P D s j hd).sampler.scalarPrefix.rows := by
  cases hr
  cases hi
  rfl

private theorem run_data_congr {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (he : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    ofState (run x cs hc)=ofState (run x ds hd) := by
  cases he
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (root ctx : List Bool) (hc : (D.rules root).length≤P.cap root+1)
  (hr : (D.rules root).length≤P.cap root+1+1)

include hc

theorem rows :
    HEq ((family P D H).state (keyAt root (D.rules root).length ctx)).sampler.scalarPrefix.rows
      (run (initial P D root) (D.rules root) hr).sampler.scalarPrefix.rows := by
  let key:=keyAt root (D.rules root).length ctx
  have H1 : HEq ((family P D H).state key).sampler.scalarPrefix.rows
      (IntegralMixedFramedFamilyRunView.runAt P D (pairFst key)
        (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _)).sampler.scalarPrefix.rows := HEq.rfl
  refine H1.trans ((rows_at_congr P D _ root _ (D.rules root).length (pairFst_pair _ _)
    (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ ctx hc) (min_le_right _ _) hc).trans ?_)
  exact run_rows_congr (initial P D root) _ _ (paddedPast_full _ _) _ hr

theorem data :
    ofState ((family P D H).state (keyAt root (D.rules root).length ctx))=
      ofState (run (initial P D root) (D.rules root) hr) := by
  let key:=keyAt root (D.rules root).length ctx
  have H1 : ofState ((family P D H).state key)=
      atRun P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _) := rfl
  refine H1.trans ((IntegralMixedFramedBankObservation.atRun_congr P D _ root _ (D.rules root).length
    (pairFst_pair _ _) (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ ctx hc)
    (min_le_right _ _) hc).trans ?_)
  exact run_data_congr (initial P D root) _ _ (paddedPast_full _ _) _ hr

end LeanCanny.Algebra.IntegralMixedFramedFullObservation
