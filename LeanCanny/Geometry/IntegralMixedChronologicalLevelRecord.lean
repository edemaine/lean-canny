/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelCommands
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelChecked

/-! # The realized chronological word fills an actually checked native level packet -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedOptionalEndpoints
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap)

def NativePair.levelRecord (side : Bool) :=IntegralMixedRoadmapLevel.packet
  (IntegralMixedChronologicalFrameCode.labels d) R.leftSpec R.rightSpec side
    (IntegralMixedRoadmapLevel.compiled n (R.levelPacket side))

theorem NativePair.levelRecord_checked (side : Bool) (hg : d.labels.length+1<n+1) :
    IntegralMixedRoadmapLevel.Checked n B (IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree)
      m (R.levelRecord side) :=by
  refine ⟨?_,?_⟩
  · simp only [IntegralMixedRoadmapLevel.Good,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
      IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.sideWord,IntegralMixedRoadmapLevel.side,
      IntegralMixedRoadmapLevel.slice,NativePair.levelRecord,IntegralMixedRoadmapLevel.packet,
      pairFst_pair,pairSnd_pair,IntegralMixedChronologicalFrameCode.labels_count]
    refine ⟨IntegralMixedChronologicalFrameCode.labels_good d,hg,R.left_good,R.right_good,?_,hcap,?_⟩
    · cases side
      · exact Or.inl rfl
      · exact Or.inr rfl
    · cases side <;> rfl
  · have HS : IntegralMixedRoadmapLevel.slice (R.levelRecord side)=
        IntegralMixedRoadmapLevel.compiled n (R.levelPacket side):=by
      simp only [IntegralMixedRoadmapLevel.slice,NativePair.levelRecord,IntegralMixedRoadmapLevel.packet,
        pairSnd_pair]
    rw [HS]
    exact IntegralMixedRoadmapLevel.compiled_packet n (IntegralMixedChronologicalFrameCode.labels d)
      R.leftSpec R.rightSpec side [] (IntegralMixedRoadmapLevel.compiled n (R.levelPacket side))

theorem NativePair.levelRecord_word (hk : d.labels.length<n+1) (g : Fin (n+1))
    (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (HG : g.val=d.labels.length+1) (side : Bool) :
    WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.slice (R.levelRecord side) :=by
  simpa only [IntegralMixedRoadmapLevel.slice,NativePair.levelRecord,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair] using R.levelWord_compiled hk g hg HG side

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
