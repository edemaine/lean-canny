/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelPhysicalReadback
/-! # Typed parent normalization for a single shared proper-level family -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalFrame IntegralMixedFrozenFrame IntegralMixedCriticalSweep
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open IntegralMixedFramedFixedContinuation IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B :ℕ} {P Q :SpatialSource n} (initial :State P S B 0 (Fin 0))
  (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (ho :older.length≤S+1)
  (actual :State Q S B older.length (IntegralMixedFramedHistoryScript.Index (Fin 0) older))
  (ha :actual=reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ)
local notation "parent"=>actual

include ha in
/-- An explicit equality of the parent state is used once; both sides keep
one pair and one midpoint anchor from the same matched family. -/
theorem exists_guarded_proper_level_at_state (d :Descriptor n older.length) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (HG :g.val=d.labels.length+1) (positive :0<n) (charge :ℕ)
    (hdegree :Q.degree=BoundedZeroSource.powerDegree charge)
    (hcapQ :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ)
    (hz :∀i,((parent).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :(parent).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((parent).sampler.scalarPrefix.basis.generator i)=z ((parent).sampler.scalar i)^weights S (2^B) older.length i)
    (values :Fin older.length→ℝ) (H :∀i,φ ((parent).bank.numerator i)/((parent).bank.denominator i:ℝ)=values i)
    (horizon :older.length+2+2+2*(n-d.labels.length)≤S+1)
    (choices :IntegralMixedRelativeCuts.Choices parent (by omega)
      (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (left right :Endpoint older.length)
    (HL :left.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (HR :right.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (hab :left.value values<right.value values)
    (M :MatchedSlabInterior parent (by omega) φ (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (IntegralMixedChronologicalSweepFrame.next d hk) (Finset.mem_insert_self _ _) g hg values
      (left.value values) (right.value values) ⟨(left.value values+right.value values)/2,by constructor <;> linarith⟩)
    (i :IntegralMixedSelectedPhysicalFiber.physical (cutSource parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (by omega) (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ
        ((left.value values+right.value values)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen
    let pMID:=M.curve i ((left.value values+right.value values)/2)∘rho.symm
    ∃R :NativePair parent d z φ values left right positive hcapQ,
      let hr :older.length+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1:=by
        have HC:=R.result.count
        have HQ:=R.orderedFree_length hk
        omega
      let hp :older.length+R.result.commands.length≤S:=by omega
      let room :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
      let hroom :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
      let childRoom :older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length≤S+1:=by omega
      ∃A :R.result.MidpointCaptures hp (IntegralMixedChronologicalSweepFrame.next d hk) g g hg hg
        pMID (R.orderedFree hk) room,∀side,
        let pChild:=M.curve i (if side then right.value values else left.value values)∘rho.symm
        ∃E :R.LevelChildCaptures hk g hg hp pMID room A hroom side pChild childRoom,
        ∃u :ℕ→ℝ,∃e :R.levelIndex hk g hg side≃Fin (IntegralMixedFramedPhysicalIndex.arity
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)),
          (IntegralMixedFramedRunObservation.ofCommands initial
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
            (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).Roots u ∧
          HEq (IntegralMixedFramedPhysicalIndex.enumerate ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)) e ∧
          (∀j :IntegralMixedFramedHistoryScript.Index (Fin 0) older,
            u (IntegralMixedFramedPhysicalIndex.enumerate older j).val=z j) ∧
          R.NaturalReadback hk g hg hp room hroom side childRoom pMID pChild A E u e
            (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial
              ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
              (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).point u j) :=by
  subst actual
  exact exists_guarded_proper_level initial hQ older ho d hk g hg HG positive charge hdegree hcapQ
    z hz φ hφ values H horizon choices left right HL HR hab M i

include ha in
/-- Package both sides from the one shared anchor before substituting native metadata. -/
theorem exists_physical_proper_level_at_state (d :Descriptor n older.length) (hk :d.labels.length<n+1)
    (g :Fin (n+1)) (hg :g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (HG :g.val=d.labels.length+1) (positive :0<n) (charge :ℕ)
    (hdegree :Q.degree=BoundedZeroSource.powerDegree charge)
    (hcapQ :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (z :IntegralMixedFramedHistoryScript.Index (Fin 0) older→ℝ)
    (hz :∀i,((parent).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ :(parent).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((parent).sampler.scalarPrefix.basis.generator i)=z ((parent).sampler.scalar i)^weights S (2^B) older.length i)
    (values :Fin older.length→ℝ) (H :∀i,φ ((parent).bank.numerator i)/((parent).bank.denominator i:ℝ)=values i)
    (horizon :older.length+2+2+2*(n-d.labels.length)≤S+1)
    (choices :IntegralMixedRelativeCuts.Choices parent (by omega)
      (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (left right :Endpoint older.length)
    (HL :left.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (HR :right.Allowed (jointEndpointSet parent (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (hab :left.value values<right.value values)
    (M :MatchedSlabInterior parent (by omega) φ (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (IntegralMixedChronologicalSweepFrame.next d hk) (Finset.mem_insert_self _ _) g hg values
      (left.value values) (right.value values) ⟨(left.value values+right.value values)/2,by constructor <;> linarith⟩)
    (i :IntegralMixedSelectedPhysicalFiber.physical (cutSource parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk))
      (by omega) (cutRule parent d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ
        ((left.value values+right.value values)/2)):
    let rho:=FrozenCoordinateOrdering.permutation (line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen
    let pMID:=M.curve i ((left.value values+right.value values)/2)∘rho.symm
    ∃R :NativePair parent d z φ values left right positive hcapQ,∀side,
      let pChild:=M.curve i (if side then right.value values else left.value values)∘rho.symm
      let hr :older.length+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1:=by
        have HC:=R.result.count
        have HQ:=R.orderedFree_length hk
        omega
      ∃u :ℕ→ℝ,
        (IntegralMixedFramedRunObservation.ofCommands initial
          ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
          (by have HH:=R.level_room hk g hg side (by omega);simp only [List.length_append,List.length_map];omega)).Roots u ∧
        R.PhysicalReadback hQ older hk g hg side hr
          (IntegralMixedFramedPhysicalIndex.arity ((R.levelCommands hk g hg side).map (wrap Q hQ)++older))
          u pMID pChild (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
            (by have HH:=R.level_room hk g hg side (by omega);simp only [List.length_append,List.length_map];omega)).point u j) ∧
        ∀j :IntegralMixedFramedHistoryScript.Index (Fin 0) older,
          u (IntegralMixedFramedPhysicalIndex.enumerate older j).val=z j:=by
  dsimp only
  obtain ⟨R,A,HE⟩:=exists_guarded_proper_level_at_state initial hQ older ho actual ha
    d hk g hg HG positive charge hdegree hcapQ z hz φ hφ values H horizon choices left right HL HR hab M i
  refine ⟨R,?_⟩
  intro side
  obtain ⟨E,u,e,hu,hen,hOld,HN⟩:=HE side
  refine ⟨u,hu,?_,hOld⟩
  unfold NativePair.PhysicalReadback
  exact ⟨A,E,e,hen,HN⟩

end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
