/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedProperLevel
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumnsBase
/-! # Exact physical column numbers of both blocks in a chronological level -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript IntegralMixedFramedFixedContinuation FlatAffineCriticalStage
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private noncomputable def onIndex {α β :Type} {L :ℕ} (h :α=β) (e :α≃Fin L):β≃Fin L:=
  (Equiv.cast h).symm.trans e
private theorem onIndex_heq {α β :Type} {L :ℕ} (h :α=β) (e :α≃Fin L):HEq e (onIndex h e):=by
  subst β
  rfl
private theorem cast_target {α :Type} {a b :ℕ} (e :α≃Fin a) (h :a=b):HEq (e.trans (finCongr h)) e:=by
  subst b
  rfl
private theorem step_heq {n B :ℕ} {P :SpatialSource n} {α β :Type} {a b :ℕ}
    (r :CriticalRule n) (e :α≃Fin a) (f :β≃Fin b) (hi :α=β) (ha :a=b) (he :HEq e f):
    HEq (stepEquiv (.critical r :Command P B) e) (stepEquiv (.critical r :Command P B) f):=by
  subst β
  subst b
  cases eq_of_heq he
  rfl
private theorem value_heq {α :Type} [Fintype α] {a b :ℕ}
    (e :α≃Fin a) (f :α≃Fin b) (he :HEq e f) (i :α):(e i).val=(f i).val:=by
  have hab :a=b:=by
    have HA:=Fintype.card_congr e
    have HB:=Fintype.card_congr f
    simp only [Fintype.card_fin] at HA HB
    exact HA.symm.trans HB
  subst b
  cases eq_of_heq he
  rfl

private noncomputable def criticalColumns {n B :ℕ} {P :SpatialSource n} {α :Type} {L :ℕ}
    (r :CriticalRule n) (e :α≃Fin L):NextIndex α (.critical r :Command P B)≃Fin (L+(2*n+4)):=
  (stepEquiv (.critical r :Command P B) e).trans (finCongr (by
    simp only [IntegralMixedFramedPhysicalIndex.added,Command.isCritical,ite_true,
      IntegralMixedFramedPhysicalIndex.block]
    omega))
private theorem critical_old {n B :ℕ} {P :SpatialSource n} {α :Type} {L :ℕ}
    (r :CriticalRule n) (e :α≃Fin L) (i :α):
    (criticalColumns (P:=P) (B:=B) r e (Sum.inl (Sum.inl i))).val=(e i).val:=rfl
private theorem critical_ambient {n B :ℕ} {P :SpatialSource n} {α :Type} {L :ℕ}
    (r :CriticalRule n) (e :α≃Fin L) (i :Fin (n+1)):
    (criticalColumns (P:=P) (B:=B) r e (Sum.inl (ambient i))).val=L+i.val:=rfl
private theorem critical_columns_heq {n B :ℕ} {P :SpatialSource n}
    (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
    (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (r :CriticalRule n)
    {α :Type} {L :ℕ} (e :α≃Fin L)
    (hi :IntegralMixedFramedHistoryScript.Index (Fin 0) older=α) (hL :arity older=L)
    (he :HEq (enumerate older) e):
    HEq (enumerate (wrap P hP (.critical r)::older)) (criticalColumns (P:=P) (B:=B) r e):=
  (step_heq r (enumerate older) e hi hL he).trans (cast_target _ _).symm

variable {n S B m :ℕ} {P :SpatialSource n}
  (hP :PurePowerReductionBounds.dimension (n+1) P.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
noncomputable local instance :Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) older):=
  IntegralMixedFramedHistoryScript.indexFintype (Fin 0) older
variable {x :State P S B m (IntegralMixedFramedHistoryScript.Index (Fin 0) older)}
  {d :Descriptor n m} {z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ}
  {φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values :Fin m→ℝ} {left right :Endpoint m}
  {hn :0<n} {hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
  (R :NativePair x d z φ values left right hn hcap) (hk :d.labels.length<n+1)
  (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
  (side :Bool)
local notation "pairCs"=>R.result.commands.map (wrap P hP)++older
local notation "L0"=>arity pairCs
local notation "K"=>List.length (NativePair.orderedFree R hk)
local notation "span"=>(2*n+4)
private noncomputable def midRule :CriticalRule n:=(R.levelMidpointData hk g hg).rule
private noncomputable def childRule :CriticalRule n:=(R.levelEndpointData hk g hg side).rule
local notation "mr"=>midRule older R hk g hg
local notation "cr"=>childRule older R hk g hg side
local notation "midOld"=>wrap P hP (Command.critical mr)::pairCs
local notation "midCs"=>List.map (wrap P hP) (NativePair.levelMidpointCommands R hk g hg)++midOld
local notation "childOld"=>wrap P hP (Command.critical cr)::midCs
local notation "finalCs"=>List.map (wrap P hP) (NativePair.levelChildCommands R hk g hg side)++childOld

private noncomputable def pairColumns :
    Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands≃Fin L0:=onIndex (index_append P hP R.result.commands older) (enumerate pairCs)
private theorem pair_columns_heq :HEq (enumerate pairCs) (pairColumns hP older R):=
  onIndex_heq _ _
private noncomputable def midAnchorColumns :
    (Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands⊕Variables (n+1))⊕Unit ≃
      Fin (L0+span):=criticalColumns (P:=P) (B:=B) mr (pairColumns hP older R)
private theorem mid_anchor_columns_heq :HEq (enumerate midOld) (midAnchorColumns hP older R hk g hg):=
  critical_columns_heq hP pairCs mr (pairColumns hP older R)
    (index_append P hP R.result.commands older) rfl (pair_columns_heq hP older R)
private noncomputable def midColumns :
    Index ((Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands⊕Variables (n+1))⊕Unit)
      (R.levelMidpointCommands hk g hg)≃Fin (L0+span+span*K):=columns (P:=P) (B:=B)
  (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
  (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
  ⟨g,R.result.free_after_pair _ g hg⟩ (midAnchorColumns hP older R hk g hg) (R.orderedFree hk)
private theorem mid_columns_heq :HEq (enumerate midCs) (midColumns hP older R hk g hg):=by
  exact companion_columns_from hP midOld _ _ _ _ _ (midAnchorColumns hP older R hk g hg)
    (congrArg (fun α :Type=>(α⊕Variables (n+1))⊕Unit) (index_append P hP R.result.commands older))
    (by simp only [arity,wrap,IntegralMixedFramedPhysicalIndex.added,Command.isCritical,ite_true,
      IntegralMixedFramedPhysicalIndex.block];omega) (mid_anchor_columns_heq hP older R hk g hg)
private noncomputable def childAnchorColumns :
    (Index ((Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands⊕Variables (n+1))⊕Unit)
      (R.levelMidpointCommands hk g hg)⊕Variables (n+1))⊕Unit ≃Fin (L0+span+span*K+span):=criticalColumns (P:=P) (B:=B) cr (midColumns hP older R hk g hg)
private theorem mid_arity :arity midCs=L0+span+span*K:=by
  rw [show R.levelMidpointCommands hk g hg=commands (P:=P) (B:=B) _ _ _ _ (R.orderedFree hk) from rfl,
    companion_arity]
  simp only [arity,wrap,IntegralMixedFramedPhysicalIndex.added,Command.isCritical,ite_true,
    IntegralMixedFramedPhysicalIndex.block]
  omega
private theorem child_anchor_columns_heq :HEq (enumerate childOld)
    (childAnchorColumns hP older R hk g hg side):=by
  apply critical_columns_heq hP midCs cr (midColumns hP older R hk g hg)
  · exact (index_append P hP (R.levelMidpointCommands hk g hg) midOld).trans
      (congrArg (fun α :Type=>Index ((α⊕Variables (n+1))⊕Unit) (R.levelMidpointCommands hk g hg))
        (index_append P hP R.result.commands older))
  · exact mid_arity hP older R hk g hg
  · exact mid_columns_heq hP older R hk g hg
private noncomputable def levelColumns :
    R.levelIndex hk g hg side≃Fin (L0+span+span*K+span+span*K):=columns (P:=P) (B:=B)
  (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
  (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
  (childAnchorColumns hP older R hk g hg side) (R.orderedFree hk)

private theorem mid_index :IntegralMixedFramedHistoryScript.Index (Fin 0) midCs=
    Index ((Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) R.result.commands⊕Variables (n+1))⊕Unit)
      (R.levelMidpointCommands hk g hg):=
  (index_append P hP (R.levelMidpointCommands hk g hg) midOld).trans
    (congrArg (fun α :Type=>Index ((α⊕Variables (n+1))⊕Unit) (R.levelMidpointCommands hk g hg))
      (index_append P hP R.result.commands older))
private theorem child_anchor_arity :arity childOld=L0+span+span*K+span:=by
  change arity midCs+IntegralMixedFramedPhysicalIndex.added (.critical cr :Command P B)=_
  rw [mid_arity hP older R hk g hg]
  simp only [IntegralMixedFramedPhysicalIndex.added,Command.isCritical,ite_true,
    IntegralMixedFramedPhysicalIndex.block]
  omega
private theorem level_columns_heq :HEq (enumerate finalCs) (levelColumns hP older R hk g hg side):=by
  exact companion_columns_from hP childOld _ _ _ _ _ (childAnchorColumns hP older R hk g hg side)
    (congrArg (fun α :Type=>(α⊕Variables (n+1))⊕Unit) (mid_index hP older R hk g hg))
    (child_anchor_arity hP older R hk g hg side) (child_anchor_columns_heq hP older R hk g hg side)
private theorem level_program_eq :(R.levelCommands hk g hg side).map (wrap P hP)++older=finalCs:=by
  simp only [NativePair.levelCommands,List.map_append,List.map_cons,List.cons_append,
    List.nil_append,List.append_assoc,midRule,childRule]
private theorem enumerate_program_eq {a B :ℕ}
    (cs ds :List (IntegralMixedFramedHistoryScript.Instruction a B)) (hcs :cs=ds):
    HEq (enumerate cs) (enumerate ds):=by
  cases hcs
  rfl
private theorem level_full_columns_heq :
    HEq (enumerate ((R.levelCommands hk g hg side).map (wrap P hP)++older))
      (levelColumns hP older R hk g hg side):=
  (enumerate_program_eq _ _ (level_program_eq hP older R hk g hg side)).trans
    (level_columns_heq hP older R hk g hg side)

theorem NativePair.level_physical_arity :
    arity ((R.levelCommands hk g hg side).map (wrap P hP)++older)=L0+span*(2+2*K):=by
  rw [level_program_eq hP older R hk g hg side]
  rw [show R.levelChildCommands hk g hg side=commands (P:=P) (B:=B) _ _ _ _ (R.orderedFree hk) from rfl,
    companion_arity]
  rw [child_anchor_arity hP older R hk g hg side]
  ring

noncomputable local instance :Fintype (R.levelIndex hk g hg side):=by
  unfold NativePair.levelIndex
  infer_instance

variable {L :ℕ} (e :R.levelIndex hk g hg side≃Fin L)
  (he :HEq (enumerate ((R.levelCommands hk g hg side).map (wrap P hP)++older)) e)
include he

theorem NativePair.level_mid_anchor_number (i :Fin (n+1)):
    (e (R.levelMidAnchorColumn hk g hg side i)).val=L0+i.val:=by
  rw [value_heq e (levelColumns hP older R hk g hg side)
    (he.symm.trans (level_full_columns_heq hP older R hk g hg side))]
  have H1:=IntegralMixedPointCompanion.columns_old (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    (childAnchorColumns hP older R hk g hg side) (R.orderedFree hk)
    (Sum.inl (Sum.inl (oldColumns (R.levelMidpointCommands hk g hg) (Sum.inl (ambient i)))))
  change (levelColumns hP older R hk g hg side (R.levelMidAnchorColumn hk g hg side i)).val=_ at H1
  rw [H1]
  change (midColumns hP older R hk g hg
    (oldColumns (R.levelMidpointCommands hk g hg) (Sum.inl (ambient i)))).val=_
  have H2:=IntegralMixedPointCompanion.columns_old (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (midAnchorColumns hP older R hk g hg) (R.orderedFree hk)
    (Sum.inl (ambient i))
  change (midColumns hP older R hk g hg
    (oldColumns (R.levelMidpointCommands hk g hg) (Sum.inl (ambient i)))).val=_ at H2
  rw [H2]
  exact critical_ambient (P:=P) (B:=B) mr (pairColumns hP older R) i

theorem NativePair.level_mid_number (k :Fin K) (i :Fin (n+1)):
    (e (R.levelMidColumn hk g hg side k i)).val=L0+span+span*(K-1-k.val)+i.val:=by
  rw [value_heq e (levelColumns hP older R hk g hg side)
    (he.symm.trans (level_full_columns_heq hP older R hk g hg side))]
  let col :Index ((Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older)
      R.result.commands⊕Variables (n+1))⊕Unit) (R.levelMidpointCommands hk g hg):=blockColumn (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) k i
  have H1:=IntegralMixedPointCompanion.columns_old (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    (childAnchorColumns hP older R hk g hg side) (R.orderedFree hk) (Sum.inl (Sum.inl col))
  change (levelColumns hP older R hk g hg side (R.levelMidColumn hk g hg side k i)).val=_ at H1
  rw [H1]
  change (midColumns hP older R hk g hg col).val=_
  exact IntegralMixedPointCompanion.columns_block (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (midAnchorColumns hP older R hk g hg) (R.orderedFree hk) k i

theorem NativePair.level_child_anchor_number (i :Fin (n+1)):
    (e (R.levelChildAnchorColumn hk g hg side i)).val=L0+span*(1+K)+i.val:=by
  rw [value_heq e (levelColumns hP older R hk g hg side)
    (he.symm.trans (level_full_columns_heq hP older R hk g hg side))]
  have H1:=IntegralMixedPointCompanion.columns_old (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    (childAnchorColumns hP older R hk g hg side) (R.orderedFree hk) (Sum.inl (ambient i))
  change (levelColumns hP older R hk g hg side (R.levelChildAnchorColumn hk g hg side i)).val=_ at H1
  rw [H1]
  have H2:=critical_ambient (P:=P) (B:=B) cr (midColumns hP older R hk g hg) i
  change (childAnchorColumns hP older R hk g hg side (Sum.inl (ambient i))).val=_ at H2
  rw [H2]
  ring

theorem NativePair.level_child_number (k :Fin K) (i :Fin (n+1)):
    (e (R.levelChildColumn hk g hg side k i)).val=L0+span*(2+K)+span*(K-1-k.val)+i.val:=by
  rw [value_heq e (levelColumns hP older R hk g hg side)
    (he.symm.trans (level_full_columns_heq hP older R hk g hg side))]
  have H:=IntegralMixedPointCompanion.columns_block (P:=P) (B:=B)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    (childAnchorColumns hP older R hk g hg side) (R.orderedFree hk) k i
  change (levelColumns hP older R hk g hg side (R.levelChildColumn hk g hg side k i)).val=_ at H
  rw [H]
  ring

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
