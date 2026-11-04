/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
/-! # Equal full parent snapshots transport the same decoded local program -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding LeanCanny.Geometry IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedOptionalEndpoints IntegralMixedFramedFixedContinuation
open scoped Classical

def Data.castProgram {d e :Data} (h :d=e) (cs :List (Command d.source d.width)):
    List (Command e.source e.width):=h▸cs

theorem Data.castProgram_length {d e :Data} (h :d=e) (cs :List (Command d.source d.width)):
    (d.castProgram h cs).length=cs.length:=by
  subst e
  rfl

theorem Data.castProgram_heq {d e :Data} (h :d=e) (cs :List (Command d.source d.width)):
    HEq (d.castProgram h cs) cs:=by
  subst e
  rfl

theorem Data.castProgram_room {d e :Data} (h :d=e) (cs :List (Command d.source d.width)):
    d.birth+cs.length≤d.horizon+1 ↔ e.birth+(d.castProgram h cs).length≤e.horizon+1:=by
  subst e
  rfl

theorem Data.decodes_cast {d e :Data} [fd :Fintype d.index] [fe :Fintype e.index]
    (h :d=e) (hd :0<d.ambient) (he :0<e.ambient)
    (hcapd :IntegralMixedExceptionalBounds.auxiliaryCap (d.ambient+1) d.source.degree≤2^d.width)
    (hcape :IntegralMixedExceptionalBounds.auxiliaryCap (e.ambient+1) e.source.degree≤2^e.width)
    (cs :List (Command d.source d.width)) (roomd :d.birth+cs.length≤d.horizon+1)
    (roome :e.birth+(d.castProgram h cs).length≤e.horizon+1) (codes :List (List Bool)):
    Decodes d.state hd hcapd cs roomd codes ↔ Decodes e.state he hcape (d.castProgram h cs) roome codes:=by
  subst e
  have HF :fd=fe:=Subsingleton.elim _ _
  cases HF
  rfl

theorem Data.continueRun_cast {d e :Data} [fd :Fintype d.index] [fe :Fintype e.index]
    (h :d=e) (cs :List (Command d.source d.width)) (roomd :d.birth+cs.length≤d.horizon+1)
    (roome :e.birth+(d.castProgram h cs).length≤e.horizon+1):
    HEq (continueRun d.state cs roomd) (continueRun e.state (d.castProgram h cs) roome):=by
  subst e
  have HF :fd=fe:=Subsingleton.elim _ _
  cases HF
  rfl

theorem Data.programIndex_cast {d e :Data} (h :d=e) (cs :List (Command d.source d.width)):
    Index d.index cs=Index e.index (d.castProgram h cs):=by
  subst e
  rfl

theorem Data.wrappedProgram_cast {d e :Data} (h :d=e)
    (hcapd :PurePowerReductionBounds.dimension (d.ambient+1) d.source.degree≤2^d.width)
    (hcape :PurePowerReductionBounds.dimension (e.ambient+1) e.source.degree≤2^e.width)
    (cs :List (Command d.source d.width)):
    HEq (cs.map (wrap d.source hcapd)) ((d.castProgram h cs).map (wrap e.source hcape)):=by
  subst e
  rfl

theorem Data.wrappedAppend_cast {d e :Data} (h :d=e)
    (hcapd :PurePowerReductionBounds.dimension (d.ambient+1) d.source.degree≤2^d.width)
    (hcape :PurePowerReductionBounds.dimension (e.ambient+1) e.source.degree≤2^e.width)
    (cs :List (Command d.source d.width))
    (older :List (IntegralMixedFramedHistoryScript.Instruction d.ambient d.width))
    (newer :List (IntegralMixedFramedHistoryScript.Instruction e.ambient e.width)) (hold :HEq older newer):
    HEq (cs.map (wrap d.source hcapd)++older)
      ((d.castProgram h cs).map (wrap e.source hcape)++newer):=by
  subst e
  cases eq_of_heq hold
  rfl

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
