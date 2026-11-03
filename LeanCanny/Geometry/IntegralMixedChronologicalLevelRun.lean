/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelCommands
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelRealization

/-! # The literal flat level run is the same actual correlated sequence of blocks -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap) (hk : d.labels.length<n+1)
  (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

noncomputable def NativePair.levelFinalState (hp : m+R.result.commands.length≤S)
    (room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
    (hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S) (side : Bool)
    (childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :=
  IntegralMixedPointCompanion.run
    (step (R.levelCapturedState hk g hg hp room) hroom (.critical (R.levelEndpointData hk g hg side).rule))
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) childRoom

theorem NativePair.level_run_heq (hp : m+R.result.commands.length≤S)
    (room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1)
    (hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S) (side : Bool)
    (childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :
    HEq (continueRun x (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom))
      (R.levelFinalState hk g hg hp room hroom side childRoom) :=by
  let cM : Command P B:=.critical (R.levelMidpointData hk g hg).rule
  let cE : Command P B:=.critical (R.levelEndpointData hk g hg side).rule
  let mc:=R.levelMidpointCommands hk g hg
  let cc:=R.levelChildCommands hk g hg side
  let cs1:=cM::R.result.commands
  let cs2:=mc++cs1
  let cs3:=cE::cs2
  have Hmc : mc.length=(R.orderedFree hk).length:=commands_length _ _ _ _ _
  have Hcc : cc.length=(R.orderedFree hk).length:=commands_length _ _ _ _ _
  have H1 : m+cs1.length≤S+1:=by simp only [cs1,List.length_cons];omega
  have H2 : m+cs2.length≤S+1:=by simp only [cs2,cs1,List.length_append,List.length_cons,Hmc];omega
  have H3 : m+cs3.length≤S+1:=by simp only [cs3,cs2,cs1,List.length_cons,List.length_append,Hmc];omega
  have H4 : m+(cc++cs3).length≤S+1:=by
    simp only [List.length_append,cs3,cs2,cs1,List.length_cons,Hmc,Hcc]
    omega
  have Hm : m+cs1.length+mc.length≤S+1:=by simp only [cs1,List.length_cons,Hmc];omega
  have Hc : m+cs3.length+cc.length≤S+1:=by
    simp only [cs3,cs2,cs1,List.length_cons,List.length_append,Hmc,Hcc]
    omega
  have HSrun:=run_continue (R.result.anchorState hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) room
  have HS : HEq (continueRun x cs2 H2) (R.levelCapturedState hk g hg hp room):=
    (continueRun_append x cs1 H1 mc H2 Hm).trans HSrun.symm
  have HT : m+cs2.length=m+R.result.commands.length+1+(R.orderedFree hk).length:=by
    simp only [cs2,cs1,List.length_append,List.length_cons,Hmc]
    omega
  have HI : Index ι cs2=Index ((Index ι R.result.commands⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit) mc:=
    index_append ι mc cs1
  have HSborn : HEq (continueRun x cs3 H3)
      (step (R.levelCapturedState hk g hg hp room) hroom cE):=
    IntegralMixedOptionalEndpoints.step_heq _ _ _ _ HT HI HS cE
  have HTborn : m+cs3.length=m+R.result.commands.length+1+(R.orderedFree hk).length+1:=by
    simp only [cs3,List.length_cons]
    omega
  have HIborn : Index ι cs3=NextIndex (Index ((Index ι R.result.commands⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit) mc) cE:=
    congrArg (fun t : Type=>NextIndex t cE) HI
  have HSchild:=continueRun_heq _ _ HTborn HIborn HSborn cc Hc
    (by simpa only [Hcc] using childRoom)
  have HSchildRun:=run_continue
    (step (R.levelCapturedState hk g hg hp room) hroom cE)
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk) childRoom
  have HF:=(continueRun_append x cs3 H3 cc H4 Hc).trans (HSchild.trans HSchildRun.symm)
  have HC : R.levelCommands hk g hg side=cc++cs3:=by
    simp only [NativePair.levelCommands,cM,cE,mc,cc,cs1,cs2,cs3,
      List.append_assoc,List.cons_append,List.nil_append]
  exact (continueRun_list_heq x _ _ (R.level_room hk g hg side childRoom) H4 HC).trans HF

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
