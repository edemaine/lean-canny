/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedGuardedCriticalColumns
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelPhysicalColumns
/-! # Endpoint physical columns persist through both later level blocks -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript IntegralMixedFramedFixedContinuation FlatAffineCriticalStage
open IntegralMixedChosenLocalRealization
open IntegralMixedFramedPhysicalIndex (arity enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem old_col_heq {n B :ℕ} {P :SpatialSource n} {α β :Type}
    (c :Command P B) (hi :α=β) (i :α) (j :β) (he :HEq i j):
    HEq (oldColumn c i) (oldColumn c j):=by
  subst β
  cases eq_of_heq he
  rfl
private theorem old_cols_heq {n B :ℕ} {P :SpatialSource n} {α β :Type}
    (cs :List (Command P B)) (hi :α=β) (i :α) (j :β) (he :HEq i j):
    HEq (oldColumns cs i) (oldColumns cs j):=by
  induction cs with
  | nil=>exact he
  | cons c cs ih=>exact old_col_heq c (congrArg (fun κ :Type=>Index κ cs) hi) _ _ ih
private theorem old_cols_append {n B :ℕ} {P :SpatialSource n} {ι :Type}
    (cs ds :List (Command P B)) (i :ι):
    HEq (oldColumns (cs++ds) i) (oldColumns cs (oldColumns ds i)):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>exact old_col_heq c (IntegralMixedOptionalEndpoints.index_append ι cs ds) _ _ ih
private theorem wrapped_old_heq {n B :ℕ} {P :SpatialSource n}
    (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (cs :List (Command P B)) (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older):
    HEq (IntegralMixedFramedPhysicalPersistence.embed (cs.map (wrap P hP)) older i) (oldColumns cs i):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have H:=old_col_heq c (IntegralMixedFramedFixedContinuation.index_append P hP cs older) _ _ ih
    cases c <;> exact H
private theorem cast_index_heq {α β :Type} (hi :α=β) (i :α):HEq (cast hi i) i:=by
  subst β
  rfl
private theorem enumeration_heq {n B :ℕ}
    (cs ds :List (IntegralMixedFramedHistoryScript.Instruction n B)) (hc :cs=ds):
    HEq (enumerate cs) (enumerate ds):=by
  cases hc
  rfl
private theorem values_heq {α β :Type} [Fintype α] {a b :ℕ}
    (e :α≃Fin a) (f :β≃Fin b) (hi :α=β) (he :HEq e f) (i :α) (j :β) (hj :HEq i j):
    (e i).val=(f j).val:=by
  subst β
  cases eq_of_heq hj
  have hab :a=b:=by
    have HA:=Fintype.card_congr e
    have HB:=Fintype.card_congr f
    simp only [Fintype.card_fin] at HA HB
    exact HA.symm.trans HB
  subst b
  cases eq_of_heq he
  rfl
private theorem retained_number {n B :ℕ}
    (newer older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    {κ :Type} {L :ℕ} (hi :IntegralMixedFramedHistoryScript.Index (Fin 0) (newer++older)=κ)
    (e :κ≃Fin L) (he :HEq (enumerate (newer++older)) e)
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older) (j :κ)
    (hj :HEq (IntegralMixedFramedPhysicalPersistence.embed newer older i) j):
    (e j).val=(enumerate older i).val:=by
  let :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (newer++older)):=
    IntegralMixedFramedHistoryScript.indexFintype (Fin 0) (newer++older)
  exact (values_heq (enumerate (newer++older)) e hi he _ _ hj).symm.trans
    (IntegralMixedFramedPhysicalPersistence.enumerate_embed newer older i)

variable {n S B m :ℕ} {P :SpatialSource n}
  (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
noncomputable local instance endpointColumnsOlderFintype :
    Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) older):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) older
variable {x :State P S B m (IntegralMixedFramedHistoryScript.Index (Fin 0) older)}
  {d :Descriptor n m} {z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {left right :Endpoint m}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
  (R :NativePair x d z φ values left right hn hcap) (hk :d.labels.length<n+1)
  (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
  (side :Bool)
local notation "pairCs"=>R.result.commands.map (wrap P hP)++older

private noncomputable def endpointOuter :List (Command P B):=
  R.levelChildCommands hk g hg side++[.critical (R.levelEndpointData hk g hg side).rule]++
    R.levelMidpointCommands hk g hg++[.critical (R.levelMidpointData hk g hg).rule]
private theorem endpoint_outer_eq :endpointOuter older R hk g hg side++R.result.commands=
    R.levelCommands hk g hg side:=by
  simp only [endpointOuter,NativePair.levelCommands,List.append_assoc]
private theorem endpoint_outer_column (p :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands):
    HEq (oldColumns (endpointOuter older R hk g hg side) p) (R.levelPairColumn hk g hg side p):=by
  let cM :Command P B:=.critical (R.levelMidpointData hk g hg).rule
  let cE :Command P B:=.critical (R.levelEndpointData hk g hg side).rule
  let mc:=R.levelMidpointCommands hk g hg
  let cc:=R.levelChildCommands hk g hg side
  have HM:=old_cols_append mc [cM] p
  have HI:=IntegralMixedOptionalEndpoints.index_append (Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands) mc [cM]
  have HE:=old_col_heq cE HI _ _ HM
  have HC:=old_cols_heq cc (congrArg (fun α :Type=>NextIndex α cE) HI) _ _ HE
  have HT:=(old_cols_append cc (cE::mc++[cM]) p).trans HC
  have HO :endpointOuter older R hk g hg side=cc++(cE::mc++[cM]):=by
    simp only [endpointOuter,cc,cE,mc,cM,List.append_assoc,List.singleton_append]
  rw [HO]
  exact HT

variable {L :ℕ} (e :R.levelIndex hk g hg side≃Fin L)
  (he :HEq (enumerate ((R.levelCommands hk g hg side).map (wrap P hP)++older)) e)
include he

theorem NativePair.level_pair_number (p :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands):
    (e (R.levelPairColumn hk g hg side p)).val=(wrappedColumns hP older R.result.commands p).val:=by
  let outer:=endpointOuter older R hk g hg side
  have HP:=IntegralMixedFramedFixedContinuation.index_append (ι:=Fin 0) P hP R.result.commands older
  let i :IntegralMixedFramedHistoryScript.Index (Fin 0) pairCs:=cast HP.symm p
  have HI :IntegralMixedFramedHistoryScript.Index (Fin 0) (outer.map (wrap P hP)++pairCs)=R.levelIndex hk g hg side:=
    (IntegralMixedFramedFixedContinuation.index_append P hP outer pairCs).trans
      ((congrArg (fun α :Type=>Index α outer) HP).trans
        ((IntegralMixedOptionalEndpoints.index_append (IntegralMixedFramedHistoryScript.Index (Fin 0) older)
          outer R.result.commands).symm.trans
            ((congrArg (Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older))
              (endpoint_outer_eq older R hk g hg side)).trans (R.level_index hk g hg side))))
  have HProgram :(R.levelCommands hk g hg side).map (wrap P hP)++older=outer.map (wrap P hP)++pairCs:=by
    rw [←endpoint_outer_eq older R hk g hg side]
    simp only [List.map_append,List.append_assoc,outer]
  have HE:HEq (enumerate (outer.map (wrap P hP)++pairCs)) e:=
    (enumeration_heq _ _ HProgram).symm.trans he
  have HRaw:HEq (IntegralMixedFramedPhysicalPersistence.embed (outer.map (wrap P hP)) pairCs i)
      (R.levelPairColumn hk g hg side p):=
    (wrapped_old_heq hP outer pairCs i).trans
      ((old_cols_heq outer HP i p (cast_index_heq HP.symm p)).trans
        (endpoint_outer_column older R hk g hg side p))
  have H:=retained_number (outer.map (wrap P hP)) pairCs HI e HE i _ HRaw
  exact H

theorem NativePair.level_endpoint_critical_number (i :ℕ) (hi :i<R.result.commands.length)
    (r :CriticalRule n) (hc :R.result.commands[i]=.critical r) (j :Fin (n+1)):
    (e (R.levelPairColumn hk g hg side (criticalAtColumn older R.result.commands i hi r hc j))).val=
      arity ((R.result.commands.drop (i+1)).map (wrap P hP)++older)+j.val:=
  (R.level_pair_number hP older hk g hg side e he _).trans
    (critical_column_number hP older R.result.commands i hi r hc j
      (wrappedColumns hP older R.result.commands) (wrapped_columns_heq hP older R.result.commands))

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
