/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalEqualLevelCaptures
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelPhysicalReadback
public import LeanCanny.Geometry.IntegralMixedChronologicalProperLevel
public import LeanCanny.Geometry.IntegralMixedGuardedProgramBirths
public import LeanCanny.Algebra.IntegralMixedFramedCompanionObservationFrom
/-! # One guarded equal-height family retains the entire old physical tuple -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open IntegralMixedOptionalEndpoints IntegralMixedPointCompanion IntegralMixedFullHistoryScript
open IntegralMixedFramedFixedContinuation IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem equal_old_column_heq {n B :ℕ} {Q :SpatialSource n} {α β :Type}
    (h :α=β) (i :α) (j :β) (hij :HEq i j) (c :Command Q B):
    HEq (IntegralMixedChosenLocalRealization.oldColumn c i) (IntegralMixedChosenLocalRealization.oldColumn c j):=by
  subst β
  cases eq_of_heq hij
  rfl

private theorem equal_wrapped_old_heq {n B :ℕ} {Q :SpatialSource n}
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (Command Q B)) (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older):
    HEq (IntegralMixedFramedPhysicalPersistence.embed (cs.map (wrap Q hQ)) older i) (oldColumns cs i):=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have H:=equal_old_column_heq (IntegralMixedFramedFixedContinuation.index_append Q hQ cs older) _ _ ih c
    cases c <;> exact H

private theorem equal_equivalence_value_heq {α β :Type} {a :ℕ} (h :α=β) (e :α≃Fin a) (f :β≃Fin a)
    (he :HEq e f) (i :α) (j :β) (hij :HEq i j):(e i).val=(f j).val:=by
  subst β
  cases eq_of_heq he
  cases eq_of_heq hij
  rfl

private theorem equal_old_number {n B :ℕ} {Q :SpatialSource n} {κ :Type}
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (cs :List (Command Q B)) (older :List (IntegralMixedFramedHistoryScript.Instruction n B))
    (hi :Index (IntegralMixedFramedHistoryScript.Index (Fin 0) older) cs=κ)
    (w :IntegralMixedFramedHistoryScript.Index (Fin 0) older→κ)
    (hw :∀i,HEq (oldColumns cs i) (w i))
    (e :κ≃Fin (IntegralMixedFramedPhysicalIndex.arity (cs.map (wrap Q hQ)++older)))
    (he :HEq (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) e)
    (i :IntegralMixedFramedHistoryScript.Index (Fin 0) older):
    (e (w i)).val=(IntegralMixedFramedPhysicalIndex.enumerate older i).val:=by
  have HV:=equal_equivalence_value_heq ((IntegralMixedFramedFixedContinuation.index_append Q hQ cs older).trans hi)
    (IntegralMixedFramedPhysicalIndex.enumerate (cs.map (wrap Q hQ)++older)) e he
    (IntegralMixedFramedPhysicalPersistence.embed (cs.map (wrap Q hQ)) older i) (w i)
    ((equal_wrapped_old_heq hQ cs older i).trans (hw i))
  exact HV.symm.trans (IntegralMixedFramedPhysicalPersistence.enumerate_embed (cs.map (wrap Q hQ)) older i)

section Actual
variable {n S B :ℕ} {P Q :SpatialSource n} (initial :State P S B 0 (Fin 0))
  (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (ho :older.length≤S+1)
local notation "parent"=>reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ

theorem exists_guarded_equal_level (d :Descriptor n older.length) (hk :d.labels.length<n+1)
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
    (he :left.value values=right.value values)
    (p :Fin (n+1)→ℝ) (HS :p∈slice Q d.frame values)
    (Hh :p (IntegralMixedChronologicalSweepFrame.next d hk)=left.value values)
    (Hgrad :∀j,j∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0):
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
        p (R.orderedFree hk) room,∀side,
        ∃E :R.LevelChildCaptures hk g hg hp p room A hroom side p childRoom,
        ∃u :ℕ→ℝ,∃e :R.levelIndex hk g hg side≃Fin (IntegralMixedFramedPhysicalIndex.arity
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)),
          (IntegralMixedFramedRunObservation.ofCommands initial
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
            (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).Roots u ∧
          HEq (IntegralMixedFramedPhysicalIndex.enumerate ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)) e ∧
          (∀j :IntegralMixedFramedHistoryScript.Index (Fin 0) older,
            u (IntegralMixedFramedPhysicalIndex.enumerate older j).val=z j) ∧
          R.NaturalReadback hk g hg hp room hroom side childRoom p p A E u e
            (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial
              ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
              (by have HH:=R.level_room hk g hg side childRoom;simp only [List.length_append,List.length_map];omega)).point u j):=by
  dsimp only
  obtain ⟨R,G⟩:=optional_pair_guarded parent (by omega) (by omega) positive charge hdegree hcapQ d hk g hg HG
    z hz φ hφ values H choices left right HL HR
  refine ⟨R,?_⟩
  have HCpair:=R.result.count
  have HQ:=R.orderedFree_length hk
  have hpR :older.length+R.result.commands.length≤S:=by omega
  have roomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S+1:=by omega
  have hroomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length≤S:=by omega
  have childRoomR :older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+
      (R.orderedFree hk).length≤S+1:=by omega
  obtain ⟨A,HE⟩:=R.exists_equal_level_captures hk g hg charge hdegree he p HS Hh Hgrad
    hpR roomR hroomR childRoomR
  refine ⟨A,?_⟩
  intro side
  obtain ⟨E⟩:=HE side
  have HM :older.length+(R.levelCommands hk g hg side).length=
      older.length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length:=by
    rw [R.levelCommands_length]
    omega
  have HS:=R.level_run_heq hk g hg hpR roomR hroomR side childRoomR
  have HO:=observe_constructed_tuple initial hQ older ho (R.levelCommands hk g hg side)
    (R.level_room hk g hg side childRoomR) (R.levelFinalState hk g hg hpR roomR hroomR side childRoomR) HM
    (R.level_index hk g hg side) HS E.captures.tuple E.captures.roots
  obtain ⟨HC,u,e,hu,hen,hcol,hpoint⟩:=HO
  refine ⟨E,u,e,hu,hen,?_,⟨G,hcol,?_⟩⟩
  · intro j
    have HN:=equal_old_number hQ (R.levelCommands hk g hg side) older (R.level_index hk g hg side)
      (fun j=>R.levelPairColumn hk g hg side (oldColumns R.result.commands j)) (R.level_old_heq hk g hg side) e hen j
    have HR:=(hcol (R.levelPairColumn hk g hg side (oldColumns R.result.commands j))).trans
      (R.captures_old_raw hk g hg hpR roomR hroomR side childRoomR _ _ A E j)
    exact (congrArg u HN.symm).trans HR
  · intro j
    have HV:=IntegralMixedCanonicalBankPoint.quotient_eq (R.levelFinalState hk g hg hpR roomR hroomR side childRoomR) HC
      _ E.captures.hom E.captures.generators j
    exact (hpoint j).trans (HV.symm.trans (E.captures.quotients j))

end Actual
section AtState
variable {n S B :ℕ} {P Q :SpatialSource n} (initial :State P S B 0 (Fin 0))
  (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
  (older :List (IntegralMixedFramedHistoryScript.Instruction n B)) (ho :older.length≤S+1)
  (actual :State Q S B older.length (IntegralMixedFramedHistoryScript.Index (Fin 0) older))
  (ha :actual=reframe (IntegralMixedFramedHistoryScript.run initial older ho) Q hQ)
local notation "parent"=>actual

include ha in
theorem exists_physical_equal_level_at_state (d :Descriptor n older.length) (hk :d.labels.length<n+1)
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
    (he :left.value values=right.value values)
    (p :Fin (n+1)→ℝ) (HS :p∈slice Q d.frame values)
    (Hh :p (IntegralMixedChronologicalSweepFrame.next d hk)=left.value values)
    (Hgrad :∀j,j∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→j≠g→
      (MvPolynomial.pderiv j (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0):
    ∃R :NativePair parent d z φ values left right positive hcapQ,∀side,
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
          u p p (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial
            ((R.levelCommands hk g hg side).map (wrap Q hQ)++older)
            (by have HH:=R.level_room hk g hg side (by omega);simp only [List.length_append,List.length_map];omega)).point u j) ∧
        ∀j :IntegralMixedFramedHistoryScript.Index (Fin 0) older,
          u (IntegralMixedFramedPhysicalIndex.enumerate older j).val=z j:=by
  subst actual
  dsimp only
  obtain ⟨R,A,HE⟩:=exists_guarded_equal_level initial hQ older ho
    d hk g hg HG positive charge hdegree hcapQ z hz φ hφ values H horizon choices left right HL HR he p HS Hh Hgrad
  refine ⟨R,?_⟩
  intro side
  obtain ⟨E,u,e,hu,hen,hOld,HN⟩:=HE side
  refine ⟨u,hu,?_,hOld⟩
  unfold NativePair.PhysicalReadback
  exact ⟨A,E,e,hen,HN⟩

end AtState
end LeanCanny.Geometry.IntegralMixedChronologicalEndpoint
