/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # The actual saved family differs from its literal run only by reframe -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

noncomputable def familyRun (P : Parameters) (D : Plan P) (key : List Bool) :=
  run (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.commands P D key)
    (by
      rw [IntegralMixedFramedHistoryFamilyBits.commands,paddedPast_length]
      exact (min_le_right _ _).trans (Nat.le_succ _))

noncomputable def stateView (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) :
    State (IntegralMixedFramedHistoryFamilyBits.instruction P D key).source
      (P.cap (pairFst key)+1) (P.width (pairFst key))
      (IntegralMixedFramedHistoryFamilyBits.commands P D key).length
      (Index (Fin 0) (IntegralMixedFramedHistoryFamilyBits.commands P D key)) :=
  (IntegralMixedFramedHistoryFamilyBits.family P D H).state key

theorem stateView_reframe (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) {r : ℕ} (R : SpatialSource r)
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width (pairFst key)) :
    reframe (stateView P D H key) R hR = reframe (familyRun P D key) R hR := rfl

theorem family_reframe (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) {r : ℕ} (R : SpatialSource r)
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width (pairFst key)) :
    reframe ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) R hR =
      reframe (familyRun P D key) R hR := rfl
noncomputable def runAt (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ)
    (hb : birth≤P.cap root+1) :=
  run (IntegralMixedFramedHistoryFamilyBits.initial P D root)
    (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth)
    (by rw [paddedPast_length]; exact hb.trans (Nat.le_succ _))

private theorem runAt_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root=root') (hb : birth=birth') (hc : birth≤P.cap root+1) (hc' : birth'≤P.cap root'+1) :
    HEq (runAt P D root birth hc) (runAt P D root' birth' hc') := by
  cases hr
  cases hb
  rfl

private theorem run_list_congr {n S B : ℕ} {Q : SpatialSource n} (initial : State Q S B 0 (Fin 0))
    (cs ds : List (Instruction n B)) (heq : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    HEq (run initial cs hc) (run initial ds hd) := by
  cases heq
  rfl

theorem familyRun_full (P : Parameters) (D : Plan P) (root context : List Bool)
    (hcap : (D.rules root).length≤P.cap root+1)
    (hcs : (D.rules root).length≤P.cap root+1+1) :
    HEq (familyRun P D (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context))
      (run (IntegralMixedFramedHistoryFamilyBits.initial P D root) (D.rules root) hcs) := by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context
  have H1 : HEq (familyRun P D key)
      (runAt P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _)) := HEq.rfl
  have H2:=runAt_congr P D (pairFst key) root (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (D.rules root).length
    (pairFst_pair _ _) (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ context hcap) (min_le_right _ _) hcap
  refine H1.trans (H2.trans ?_)
  exact run_list_congr (IntegralMixedFramedHistoryFamilyBits.initial P D root) _ _
    (paddedPast_full _ _) _ hcs

noncomputable def reframeRunAt (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ)
    (hb : birth≤P.cap root+1) {r : ℕ} (R : SpatialSource r)
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width root) :=
  reframe (runAt P D root birth hb) R hR

private theorem reframeRunAt_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root=root') (hb : birth=birth') (hc : birth≤P.cap root+1) (hc' : birth'≤P.cap root'+1)
    {r : ℕ} (R : SpatialSource r)
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width root)
    (hR' : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width root') :
    HEq (reframeRunAt P D root birth hc R hR) (reframeRunAt P D root' birth' hc' R hR') := by
  cases hr
  cases hb
  rfl

private theorem reframe_run_list_congr {n S B r : ℕ} {Q : SpatialSource n} (initial : State Q S B 0 (Fin 0))
    (cs ds : List (Instruction n B)) (heq : cs=ds) (hc : cs.length≤S+1) (hd : ds.length≤S+1)
    (R : SpatialSource r) (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^B) :
    HEq (reframe (run initial cs hc) R hR) (reframe (run initial ds hd) R hR) := by
  cases heq
  rfl

theorem familyRun_reframe_full (P : Parameters) (D : Plan P) (root context : List Bool)
    (hcap : (D.rules root).length≤P.cap root+1)
    (hcs : (D.rules root).length≤P.cap root+1+1)
    {r : ℕ} (R : SpatialSource r)
    (hRkey : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width
      (pairFst (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context)))
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width root) :
    HEq (reframe (familyRun P D (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context)) R hRkey)
      (reframe (run (IntegralMixedFramedHistoryFamilyBits.initial P D root) (D.rules root) hcs) R hR) := by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context
  have H1 : HEq (reframe (familyRun P D key) R hRkey)
      (reframeRunAt P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (min_le_right _ _) R hRkey) := HEq.rfl
  have H2:=reframeRunAt_congr P D (pairFst key) root (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (D.rules root).length
    (pairFst_pair _ _) (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ context hcap) (min_le_right _ _) hcap R hRkey hR
  refine H1.trans (H2.trans ?_)
  exact reframe_run_list_congr (IntegralMixedFramedHistoryFamilyBits.initial P D root) _ _
    (paddedPast_full _ _) _ hcs R hR
theorem stateView_reframe_full (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root context : List Bool)
    (hcap : (D.rules root).length≤P.cap root+1)
    (hcs : (D.rules root).length≤P.cap root+1+1)
    {r : ℕ} (R : SpatialSource r)
    (hRkey : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width
      (pairFst (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context)))
    (hR : PurePowerReductionBounds.dimension (r+1) R.degree≤2^P.width root) :
    HEq (reframe (stateView P D H (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context)) R hRkey)
      (reframe (run (IntegralMixedFramedHistoryFamilyBits.initial P D root) (D.rules root) hcs) R hR) :=
  (heq_of_eq (stateView_reframe P D H _ R hRkey)).trans
    (familyRun_reframe_full P D root context hcap hcs R hRkey hR)

noncomputable def indexAt (P : Parameters) (D : Plan P) (root : List Bool) (birth : ℕ) : Type :=
  Index (Fin 0) (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root) birth)

private theorem indexAt_congr (P : Parameters) (D : Plan P) (root root' : List Bool) (birth birth' : ℕ)
    (hr : root=root') (hb : birth=birth') : indexAt P D root birth=indexAt P D root' birth' := by
  cases hr
  cases hb
  rfl

theorem commands_index_full (P : Parameters) (D : Plan P) (root context : List Bool)
    (hcap : (D.rules root).length≤P.cap root+1) :
    Index (Fin 0) (IntegralMixedFramedHistoryFamilyBits.commands P D
      (IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context))=Index (Fin 0) (D.rules root) := by
  let key:=IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length context
  have H1 : Index (Fin 0) (IntegralMixedFramedHistoryFamilyBits.commands P D key)=
      indexAt P D (pairFst key) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) := rfl
  have H2:=indexAt_congr P D (pairFst key) root (IntegralMixedFramedHistoryFamilyBits.prefixLength P key) (D.rules root).length
    (pairFst_pair _ _) (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ context hcap)
  have H3:=congrArg (Index (Fin 0)) (paddedPast_full (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) (D.rules root))
  exact H1.trans (H2.trans H3)
end LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
