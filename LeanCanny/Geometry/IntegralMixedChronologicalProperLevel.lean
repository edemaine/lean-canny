/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelRun

/-! # One proper slab produces the exact canonical native level program

The midpoint and endpoint blocks use one matched family and one anchor.
All decoder receipts are derived; the geometric witnesses are constructed
from that family rather than required as an additional input oracle.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralHistorySampler UniformIntegralPowerSchedule
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {left right : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values left right hn hcap) (hk : d.labels.length<n+1)
  (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

theorem NativePair.level_length_original (side : Bool) :
    (R.levelCommands hk g hg side).length=left.freshCount+right.freshCount+2+2*(n-d.labels.length) :=by
  rw [R.levelCommands_length,R.count,R.orderedFree_length]
  omega

theorem NativePair.exists_proper_level (hm : m≤S) (charge : ℕ)
    (hdegree : P.degree=BoundedZeroSource.powerDegree charge) (HG : g.val=d.labels.length+1)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (hab : left.value values<right.value values)
    (M : MatchedSlabInterior x hm φ (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (IntegralMixedChronologicalSweepFrame.next d hk) (Finset.mem_insert_self _ _) g hg values
      (left.value values) (right.value values) ⟨(left.value values+right.value values)/2,by constructor <;> linarith⟩)
    (i : IntegralMixedSelectedPhysicalFiber.physical (cutSource x d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      hm (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ ((left.value values+right.value values)/2))
    (horizon : m+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1) :
    let hp : m+R.result.commands.length≤S:=by omega
    let room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
    let hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
    let childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1:=by omega
    let e:=FrozenCoordinateOrdering.permutation (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen
    let p:=M.curve i ((left.value values+right.value values)/2)∘e.symm
    ∃ A : R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room,∀side,
      ∃ _E : R.LevelChildCaptures hk g hg hp p room A hroom side
        (M.curve i (if side then right.value values else left.value values)∘e.symm) childRoom,
        Decodes x hn hcap (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom)
          (R.levelCodes hk g hg side) ∧
        WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled n (R.levelPacket side) ∧
        HEq (continueRun x (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom))
          (R.levelFinalState hk g hg hp room hroom side childRoom) ∧
        (R.levelCommands hk g hg side).length=left.freshCount+right.freshCount+2+2*(n-d.labels.length) :=by
  dsimp only
  obtain ⟨A,HE⟩:=R.exists_matched_level_captures hk g hg hm charge hdegree H hab M i
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨A,?_⟩
  intro side
  obtain ⟨E⟩:=HE side
  exact ⟨E,R.level_decodes hk g hg side (R.level_room hk g hg side (by omega)),
    R.levelWord_compiled hk g hg HG side,R.level_run_heq hk g hg (by omega) (by omega) (by omega) side (by omega),
    R.level_length_original hk g hg side⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
