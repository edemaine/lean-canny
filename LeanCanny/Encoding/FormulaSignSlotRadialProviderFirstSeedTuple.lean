/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedPrelude
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumns
public import LeanCanny.Geometry.IntegralMixedChronologicalSeedProgram
/-! # One genuine critical point realizes every provider seed block -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry LeanCanny.Connectivity
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedFramedPhysicalIndex IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem seed_tuple {n S B : ℕ} {V : SpatialSource n}
    (initial : State V S B 0 (Fin 0)) (Q : SpatialSource n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (older : List (Instruction n B)) (ho : older.length≤S+1)
    (hn : 0<n) (charge : ℕ) (hdegree : Q.degree=BoundedZeroSource.powerDegree charge)
    (v : ℕ→ℝ)
    (HI : IntegralMixedIntegerRealization.Realizes
      (reframe (run initial older ho) Q (IntegralMixedStaticRecordPrefix.cap Q hcap)) v)
    (p : Fin (n+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂ (Int.castRingHom ℝ) p=0)
    (t : ℕ)
    (room : older.length+(IntegralMixedChronologicalSeedProgram.selections n older.length t).length≤S+1) :
    let d := IntegralMixedChronologicalSeedProgram.descriptor n older.length
    let g := IntegralMixedChronologicalSeedProgram.zero n older.length
    let js := IntegralMixedChronologicalSeedProgram.selections n older.length t
    let cs := IntegralMixedPointCompanion.commands (P:=Q) (B:=B) d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g js
    let O := ofCommands initial
      (cs.map (IntegralMixedFramedFixedContinuation.wrap Q (IntegralMixedStaticRecordPrefix.cap Q hcap))++older)
      (by dsimp only [cs]; simp only [List.length_append,List.length_map,IntegralMixedPointCompanion.commands_length];simpa only [js,Nat.add_comm] using room)
    ∃u : ℕ→ℝ,O.Roots u ∧
      (∀k : Fin js.length,∀i : Fin (n+1),
        u (arity older+(2*n+4)*(js.length-1-k.val)+i.val)^
          UniformIntegralPowerSchedule.physical S (2^B) (older.length+(js.length-1-k.val))=p i) ∧
      ∀i : Fin (older.length+js.length),O.point u i.val=
        IntegralMixedPointCompanion.values p (fun j : Fin older.length=>v j.val) js i := by
  let x := reframe (run initial older ho) Q (IntegralMixedStaticRecordPrefix.cap Q hcap)
  let d := IntegralMixedChronologicalSeedProgram.descriptor n older.length
  let g := IntegralMixedChronologicalSeedProgram.zero n older.length
  let js := IntegralMixedChronologicalSeedProgram.selections n older.length t
  obtain ⟨z,φ,hz,hφ,hv⟩ := HI
  have HC := @IntegralMixedChronologicalSeedProgram.exists_realized_seed n S B older.length Q
    (Index (Fin 0) older) (indexFintype (Fin 0) older) x hn charge hdegree hcap z hz φ hφ
    (fun j : Fin older.length=>v j.val) hv p hp hg t room
  obtain ⟨⟨R⟩,_⟩ := HC
  obtain ⟨u,hu,_,hblocks,hpoint⟩ := @IntegralMixedFramedFixedContinuation.companion_observation n B Q n S B V
    initial Q (IntegralMixedStaticRecordPrefix.cap Q hcap) older ho d.frame.frozen (fun _=>false)
    (fun i=>.single (d.atom i)) g z φ (fun j : Fin older.length=>v j.val) p js room R
  exact ⟨u,hu,hblocks,hpoint⟩

private theorem observation_eq {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd := by cases he;rfl

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.plan
local notation "Q" r => FormulaSignSlotRadialProviderRecordPlan.spatial r

noncomputable def charge (c : List Bool) :=
  (CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderIntegerPlan.original c)).toData.size

theorem degree_power (c : List Bool) : (Q (root c)).degree=BoundedZeroSource.powerDegree (charge c) := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree CanonicalAuxiliaryCandidateCover.equation
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root c))=_
  rw [root_provider]
  rfl

theorem selection_room (c : List Bool) : (older c).length+(selections c).length≤(P).cap (root c)+1+1 := by
  rw [←commands_length]
  exact program_room c

noncomputable def observation (c : List Bool) := ofCommands (initial P D (root c)) ((D).rules (root c))
  (by have H := (D).room (root c);omega)

def TupleReceipt (c : List Bool) (v : ℕ→ℝ) (p : Fin ((P).ambient (root c)+1)→ℝ) : Prop :=
  ∃u : ℕ→ℝ,(observation c).Roots u ∧
    (∀k : Fin (selections c).length,∀i : Fin ((P).ambient (root c)+1),
      u (arity (older c)+(2*(P).ambient (root c)+4)*((selections c).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (root c)+1) (2^(P).width (root c))
          ((older c).length+((selections c).length-1-k.val))=p i) ∧
    ∀i : Fin ((older c).length+(selections c).length),(observation c).point u i.val=
      IntegralMixedPointCompanion.values p
        (fun j : Fin (older c).length=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j.val)) (selections c) i

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source

theorem exists_tuple (c : List Bool) (v : ℕ→ℝ)
    (hv : ∀i<FormulaSignSlotRadialProviderRecordPlan.count (root c),
      (FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (v i)=0)
    (p : Fin ((P).ambient (root c)+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (Q (root c)).low (Q (root c)).leading (Q (root c)).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (root c)).low (Q (root c)).leading (Q (root c)).degree)).eval₂
        (Int.castRingHom ℝ) p=0) : TupleReceipt c v p := by
  have HI := state_realizes c v hv
  have HC := seed_tuple (initial P D (root c)) (Q (root c)) (sourceCap c) (older c)
    (by rw [older_length];have H := FormulaSignSlotRadialProviderRecordPlan.room (root c);omega)
    (FormulaSignSlotRadialProviderRecordPlan.positive (root c)) (charge c) (degree_power c)
    (fun j=>v (FormulaSignSlotRadialProviderRecordPlan.count (root c)-1-j)) HI p hp hg (tail c) (selection_room c)
  obtain ⟨u,hu,hblocks,hpoint⟩ := HC
  have HR : ((D).rules (root c)).length≤(P).cap (root c)+1+1 := by
    have H := (D).room (root c)
    omega
  have HL := congrArg List.length (full_commands c)
  have HO := observation_eq (initial P D (root c)) ((D).rules (root c))
    ((commands c).map (IntegralMixedFramedFixedContinuation.wrap (Q (root c))
      (IntegralMixedStaticRecordPrefix.cap (Q (root c)) (sourceCap c)))++older c)
    HR (HL.symm.le.trans HR) (full_commands c)
  refine ⟨u,?_,hblocks,?_⟩
  · exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots u) HO).mpr hu
  · intro i
    exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point u i.val) HO).trans (hpoint i)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
