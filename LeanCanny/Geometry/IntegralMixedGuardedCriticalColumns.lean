/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCriticalAt
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAncestry
public import LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
/-! # A guarded critical coordinate has its literal oldest-first column -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedOptionalEndpoints
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedChosenLocalRealization IntegralMixedFramedFixedContinuation
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem columnCast_heq {α β :Type} {L :ℕ} (h :α=β) (e :α≃Fin L):
    HEq e ((Equiv.cast h).symm.trans e):=by
  subst β
  rfl
private theorem column_step_heq {n B :ℕ} {P :SpatialSource n} {α β :Type} {a b :ℕ}
    (c :Command P B) (e :α≃Fin a) (f :β≃Fin b) (hi :α=β) (ha :a=b) (he :HEq e f):
    HEq (stepEquiv c e) (stepEquiv c f):=by
  subst β
  subst b
  cases eq_of_heq he
  rfl
private theorem column_value_heq {α :Type} [Fintype α] {a b :ℕ}
    (e :α≃Fin a) (f :α≃Fin b) (he :HEq e f) (i :α):(e i).val=(f i).val:=by
  have hab :a=b:=by
    have HA:=Fintype.card_congr e
    have HB:=Fintype.card_congr f
    simp only [Fintype.card_fin] at HA HB
    exact HA.symm.trans HB
  subst b
  cases eq_of_heq he
  rfl
private theorem column_step_old {n B :ℕ} {P :SpatialSource n} {α :Type} {a :ℕ}
    (c :Command P B) (e :α≃Fin a) (i :α):
    (stepEquiv c e (oldColumn c i)).val=(e i).val:=by
  cases c <;> rfl

variable {n B :ℕ} {P :SpatialSource n}
  (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
noncomputable local instance guardedColumnsOlderFintype :
    Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) older):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) older

noncomputable def wrappedColumns (cs :List (Command P B)):
    Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs≃
      Fin (arity (cs.map (wrap P hP)++older)):=
  (Equiv.cast (IntegralMixedFramedFixedContinuation.index_append P hP cs older)).symm.trans
    (enumerate (cs.map (wrap P hP)++older))
theorem wrapped_columns_heq (cs :List (Command P B)):
    HEq (enumerate (cs.map (wrap P hP)++older)) (wrappedColumns hP older cs):=
  columnCast_heq _ _
private theorem wrapped_step_heq (c :Command P B) (cs :List (Command P B)):
    HEq (enumerate ((c::cs).map (wrap P hP)++older)) (stepEquiv c (wrappedColumns hP older cs)):=
  column_step_heq c (enumerate (cs.map (wrap P hP)++older)) (wrappedColumns hP older cs)
    (IntegralMixedFramedFixedContinuation.index_append P hP cs older) rfl (wrapped_columns_heq hP older cs)
private theorem wrapped_step_value (c :Command P B) (cs :List (Command P B)) {L :ℕ}
    (e :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) (c::cs)≃Fin L)
    (he :HEq (enumerate ((c::cs).map (wrap P hP)++older)) e)
    (j :NextIndex (Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs) c):
    (e j).val=(stepEquiv c (wrappedColumns hP older cs) j).val:=
  column_value_heq e _ (he.symm.trans (wrapped_step_heq hP older c cs)) j

def criticalAtColumn (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length)
    (r :CriticalRule n) (hc :cs[i]=.critical r) (j :Fin (n+1)):
    Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs:=
  cutAtColumn cs i hi (cast (congrArg
    (NextIndex (Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) (cs.drop (i+1)))) hc.symm)
    (Sum.inl (FlatAffineCriticalStage.ambient j)))

theorem critical_column_number (cs :List (Command P B)) (i :ℕ) (hi :i<cs.length)
    (r :CriticalRule n) (hc :cs[i]=.critical r) (j :Fin (n+1)) {L :ℕ}
    (e :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs≃Fin L)
    (he :HEq (enumerate (cs.map (wrap P hP)++older)) e):
    (e (criticalAtColumn older cs i hi r hc j)).val=
      arity ((cs.drop (i+1)).map (wrap P hP)++older)+j.val:=by
  induction cs generalizing i L with
  | nil=>simp only [List.length_nil] at hi;omega
  | cons c cs ih=>
    cases i with
    | zero=>
      change c=.critical r at hc
      subst c
      change (e (Sum.inl (FlatAffineCriticalStage.ambient j))).val=arity (cs.map (wrap P hP)++older)+j.val
      exact (wrapped_step_value hP older (.critical r) cs e he _).trans
        (IntegralMixedFramedPhysicalIndex.step_ambient r (wrappedColumns hP older cs) j)
    | succ i=>
      have hi' :i<cs.length:=by simpa using hi
      have HC :cs[i]=.critical r:=hc
      change (e (oldColumn c (criticalAtColumn older cs i hi' r HC j))).val=_
      exact (wrapped_step_value hP older c cs e he _).trans
        ((column_step_old c (wrappedColumns hP older cs) _).trans
          (ih i hi' HC (wrappedColumns hP older cs) (wrapped_columns_heq hP older cs)))

def criticalCoordinate (r :CriticalRule n):Fin (n+1):=
  ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
    (IntegralMixedCriticalRoot.coordinate r)
theorem criticalCoordinate_val (r :CriticalRule n):
    (criticalCoordinate r).val=r.offset.val+r.coordinate%(n-r.offset.val+1):=rfl

theorem selectedPhysical_critical {S m :ℕ} {ι :Type} [Fintype ι]
    (x :State P S B m ι) (hm :m≤S) (r :CriticalRule n)
    (y :NextIndex ι (.critical r :Command P B)→ℝ):
    selectedPhysical x hm (.critical r) y=
      y (Sum.inl (FlatAffineCriticalStage.ambient (criticalCoordinate r)))^
        UniformIntegralPowerSchedule.physical S (2^B) m:=rfl

theorem selectedPhysical_of_critical {S m :ℕ} {ι :Type} [Fintype ι]
    (x :State P S B m ι) (hm :m≤S) (c :Command P B) (y :NextIndex ι c→ℝ)
    (r :CriticalRule n) (hc :c=.critical r):
    selectedPhysical x hm c y=
      y (cast (congrArg (NextIndex ι) hc.symm)
        (Sum.inl (FlatAffineCriticalStage.ambient (criticalCoordinate r))))^
          UniformIntegralPowerSchedule.physical S (2^B) m:=by
  subst c
  exact selectedPhysical_critical x hm r y

theorem selectedPhysical_at_column {S m :ℕ}
    (x :State P S B m (IntegralMixedFramedHistoryScript.Index (Fin 0) older))
    (cs :List (Command P B)) (room :m+cs.length≤S+1)
    (y :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs→ℝ)
    (i :ℕ) (hi :i<cs.length) (r :CriticalRule n) (hc :cs[i]=.critical r):
    selectedPhysical (continueRun x (cs.drop (i+1)) (cutAt_room cs room i))
        (cutAt_fit cs room i hi) cs[i] (cutAtTuple cs i hi y)=
      y (criticalAtColumn older cs i hi r hc (criticalCoordinate r))^
        UniformIntegralPowerSchedule.physical S (2^B) (m+(cs.drop (i+1)).length):=by
  simpa only [criticalAtColumn,cutAtTuple,Function.comp_apply] using
    selectedPhysical_of_critical (continueRun x (cs.drop (i+1)) (cutAt_room cs room i))
      (cutAt_fit cs room i hi) cs[i] (cutAtTuple cs i hi y) r hc

end LeanCanny.Geometry.IntegralMixedOptionalEndpoints
