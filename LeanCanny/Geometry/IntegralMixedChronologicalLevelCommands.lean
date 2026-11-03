/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelCodes
public import LeanCanny.Geometry.IntegralMixedPointCompanionDecoded

/-! # Exact flat commands, count and decoder receipt for one native level -/
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

noncomputable def NativePair.levelMidpointCommands : List (Command P B) :=
  commands (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk))
    (shiftRows (R.levelMidpointRows hk) 1) ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk)
noncomputable def NativePair.levelChildCommands (side : Bool) : List (Command P B) :=
  commands (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (fun _=>false) (shiftRows (R.levelEndpointRows hk side) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ (R.orderedFree hk)
noncomputable def NativePair.levelCommands (side : Bool) : List (Command P B) :=
  R.levelChildCommands hk g hg side++[.critical (R.levelEndpointData hk g hg side).rule]++
    R.levelMidpointCommands hk g hg++[.critical (R.levelMidpointData hk g hg).rule]++R.result.commands

theorem NativePair.levelCodes_length (side : Bool) :
    (R.levelCodes hk g hg side).length=R.result.commands.length+2+2*(R.orderedFree hk).length :=by
  simp only [NativePair.levelCodes,NativePair.levelChildCodes,NativePair.levelMidpointCodes,
    List.length_append,List.length_singleton,IntegralMixedPointCompanion.codes_length,R.result.code_count]
  omega

theorem NativePair.levelCommands_length (side : Bool) :
    (R.levelCommands hk g hg side).length=R.result.commands.length+2+2*(R.orderedFree hk).length :=by
  simp only [NativePair.levelCommands,NativePair.levelChildCommands,NativePair.levelMidpointCommands,
    List.length_append,List.length_singleton,commands_length]
  omega

theorem NativePair.levelCount_native (side : Bool) :
    (R.levelCommands hk g hg side).length=IntegralMixedRoadmapLevel.emittedCount n (R.levelPacket side) :=by
  rw [R.levelCommands_length,R.orderedFree_length,R.native_count]
  simp only [IntegralMixedRoadmapLevel.emittedCount,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,NativePair.levelPacket,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair,IntegralMixedChronologicalFrameCode.labels_count]

theorem NativePair.level_room (side : Bool)
    (childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1) :
    m+(R.levelCommands hk g hg side).length≤S+1 :=by
  rw [R.levelCommands_length]
  omega

/-- Decoder correctness needs only the represented pair and the exact typed
critical records. Geometric captures are used to realize roots, not supplied
as a premise for the native command receipt. -/
theorem NativePair.level_decodes (side : Bool)
    (hfull : m+(R.levelCommands hk g hg side).length≤S+1) :
    Decodes x hn hcap (R.levelCommands hk g hg side) hfull (R.levelCodes hk g hg side) :=by
  let cM : Command P B:=.critical (R.levelMidpointData hk g hg).rule
  let cE : Command P B:=.critical (R.levelEndpointData hk g hg side).rule
  let mc:=R.levelMidpointCommands hk g hg
  let cc:=R.levelChildCommands hk g hg side
  let midCodes:=R.levelMidpointCodes hk g hg
  let childCodes:=R.levelChildCodes hk g hg side
  let cs1:=cM::R.result.commands
  let cs2:=mc++cs1
  let cs3:=cE::cs2
  let codes1:=(R.levelMidpointData hk g hg).code::R.result.codes
  let codes2:=midCodes++codes1
  let codes3:=(R.levelEndpointData hk g hg side).code::codes2
  have HF : m+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1:=by
    rw [R.levelCommands_length] at hfull
    omega
  have Hmc : mc.length=(R.orderedFree hk).length:=commands_length _ _ _ _ _
  have Hcc : cc.length=(R.orderedFree hk).length:=commands_length _ _ _ _ _
  have H1 : m+cs1.length≤S+1:=by simp only [cs1,List.length_cons];omega
  have H2 : m+cs2.length≤S+1:=by simp only [cs2,cs1,List.length_append,List.length_cons,Hmc];omega
  have H3 : m+cs3.length≤S+1:=by simp only [cs3,cs2,cs1,List.length_cons,List.length_append,Hmc];omega
  have H4 : m+(cc++cs3).length≤S+1:=by
    simp only [List.length_append,cs3,cs2,cs1,List.length_cons,Hmc,Hcc]
    omega
  have HD1 : Decodes x hn hcap cs1 H1 codes1:=
    Decodes.prepend_critical x hn hcap R.result.commands R.result.room R.result.codes R.result.decode
      (R.levelMidpointData hk g hg) rfl H1
  have HD2 : Decodes x hn hcap cs2 H2 codes2:=decodes_append x
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen)
    (midpointDouble (IntegralMixedChronologicalSweepFrame.next d hk)) (shiftRows (R.levelMidpointRows hk) 1)
    ⟨g,R.result.free_after_pair _ g hg⟩ hn hcap cs1 H1 codes1 HD1 rfl (R.orderedFree hk) H2
  have HB : m+R.result.commands.length+1+(R.orderedFree hk).length=m+cs2.length:=by
    simp only [cs2,cs1,List.length_append,List.length_cons,Hmc]
    omega
  have HD3 : Decodes x hn hcap cs3 H3 codes3:=
    Decodes.prepend_critical x hn hcap cs2 H2 codes2 HD2 (R.levelEndpointData hk g hg side) HB H3
  have HC : m+R.result.commands.length+1+(R.orderedFree hk).length+1=m+cs3.length:=by
    simp only [cs3,List.length_cons]
    omega
  have HD4 : Decodes x hn hcap (cc++cs3) H4 (childCodes++codes3):=decodes_append x
    (insert (IntegralMixedChronologicalSweepFrame.next d hk) R.result.frame.frozen) (fun _=>false)
    (shiftRows (R.levelEndpointRows hk side) 1) ⟨g,R.result.free_after_pair _ g hg⟩
    hn hcap cs3 H3 codes3 HD3 HC (R.orderedFree hk) H4
  simpa only [NativePair.levelCommands,NativePair.levelCodes,cs1,cs2,cs3,codes1,codes2,codes3,
    cM,cE,mc,cc,midCodes,childCodes,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using HD4

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
