/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalProperLevel
public import LeanCanny.Geometry.IntegralMixedDegenerateEndpointCaptures

/-! # The canonical level program descends at the same actual critical point

Both endpoint specifications refer to the same original endpoint. No empty
open slab, regularity, matched family, Near or point-capture oracle is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame IntegralMixedOptionalEndpoints IntegralMixedPointCompanion
open IntegralMixedFullHistoryScript Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable {x : State P S B m ι} {d : Descriptor n m} {z : ι→ℝ}
  {φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ} {values : Fin m→ℝ} {endpoint : Endpoint m}
  {hn : 0<n} {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B}
variable (R : NativePair x d z φ values endpoint endpoint hn hcap)
  (hk : d.labels.length<n+1) (g : Fin (n+1))
  (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)

theorem NativePair.exists_degenerate_level (charge : ℕ)
    (hdegree : P.degree=BoundedZeroSource.powerDegree charge) (HG : g.val=d.labels.length+1)
    (p : Fin (n+1)→ℝ) (HS : p∈slice P d.frame values)
    (Hh : p (IntegralMixedChronologicalSweepFrame.next d hk)=endpoint.value values)
    (Hgrad : ∀i,i∉d.frame.frozen→i≠IntegralMixedChronologicalSweepFrame.next d hk→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) p=0)
    (horizon : m+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1) :
    let hp : m+R.result.commands.length≤S:=by omega
    let room : m+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
    let hroom : m+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
    let childRoom : m+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1:=by omega
    ∃A : R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
      p (R.orderedFree hk) room,∀side,
      ∃_E : R.LevelChildCaptures hk g hg hp p room A hroom side p childRoom,
        Decodes x hn hcap (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom)
          (R.levelCodes hk g hg side) ∧
        WordList.encode (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.compiled n (R.levelPacket side) ∧
        HEq (continueRun x (R.levelCommands hk g hg side) (R.level_room hk g hg side childRoom))
          (R.levelFinalState hk g hg hp room hroom side childRoom) ∧
        (R.levelCommands hk g hg side).length=2*endpoint.freshCount+2+2*(n-d.labels.length) :=by
  dsimp only
  let h:=IntegralMixedChronologicalSweepFrame.next d hk
  have hh : h∉d.frame.frozen:=IntegralMixedChronologicalSweepFrame.next_free d hk
  have hfirst : h.val=d.frame.frozen.card:=d.frozen_card.symm
  obtain ⟨A,HE⟩:=R.result.exists_degenerate_program charge hdegree h hfirst hh g g hg hg p HS Hh
    (critical_after_freezing h g p Hgrad) (by omega) (R.orderedFree hk) (by omega) (by omega) (by omega)
  refine ⟨A,?_⟩
  intro side
  obtain ⟨E⟩:=HE side
  have E' : R.LevelChildCaptures hk g hg (by omega) p (by omega) A (by omega) side p (by omega):=by
    exact E
  have Hcount : (R.levelCommands hk g hg side).length=2*endpoint.freshCount+2+2*(n-d.labels.length):=by
    rw [R.level_length_original hk g hg side]
    omega
  exact ⟨E',R.level_decodes hk g hg side (R.level_room hk g hg side (by omega)),
    R.levelWord_compiled hk g hg HG side,R.level_run_heq hk g hg (by omega) (by omega) (by omega) side (by omega),Hcount⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
