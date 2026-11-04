/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedInstruction
public import LeanCanny.Algebra.IntegralMixedFramedFixedTupleObservation
/-! # Constructed local tuples satisfy the actual natural marked-prefix rows

The literal command receipt is applied before extracting ordinary natural
row data. This retains every physical variable without transporting any
complete sampler word across roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_eq {n S B :ℕ} {Q :SpatialSource n}
    (initial :State Q S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands initial cs hc=ofCommands initial ds hd:=by cases he;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "positive" root=>IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root
local notation "cap" root=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root
local notation "count" root=>IntegralMixedCausalRecordPlanBits.count root
local notation "code" root=>IntegralMixedCausalRecordPlanBits.code root
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap

noncomputable def afterObservation (root :List Bool) (j :ℕ) (codes :List (List Bool))
    (hj :j+codes.length≤count root):=
  IntegralFramedPhysicalPrefixObservation.atRoot P D root (number n root+8+j+codes.length)
    (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega))

noncomputable def wrappedCommands (root :List Bool) (j :ℕ) (jgood :j≤count root)
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root))) :
    List (Instruction ((P).ambient root) ((P).width root)):=
  (cs.map (IntegralMixedFramedFixedContinuation.wrap (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))) :
    List (Instruction ((P).ambient root) ((P).width root)))++
      IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood

theorem exists_observation (root :List Bool) (j :ℕ) (jgood :j≤count root) (codes :List (List Bool))
    (hj :j+codes.length≤count root)
    (hw :∀i,i<codes.length→(code root) (j+i)=(codes.reverse[i]?).getD [])
    (cs :List (IntegralMixedFullHistoryScript.Command (Q root) ((P).width root)))
    (hc :(IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood).length+
      cs.length≤(P).cap root+1+1)
    (HD :IntegralMixedOptionalEndpoints.Decodes (state hn ht ha hR0 root j jgood)
      (positive root) (cap root) cs hc codes)
    (tuple :IntegralMixedFullHistoryScript.Index
      (Index (Fin 0) (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood)) cs→ℝ)
    (hz :∀i :IntegralMixedFullHistoryScript.Index
      (Index (Fin 0) (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood)) cs,
      ((IntegralMixedFullHistoryScript.continueRun (state hn ht ha hR0 root j jgood) cs hc).sampler.rows i).eval₂
        (Int.castRingHom ℝ) tuple=0) :
    ∃u :ℕ→ℝ,∃y :Index (Fin 0) (wrappedCommands hn ht ha hR0 root j jgood cs)→ℝ,
      HEq y tuple ∧ (afterObservation hn ht ha hR0 root j codes hj).Roots u ∧
      ∀i,u (IntegralMixedFramedPhysicalIndex.enumerate (wrappedCommands hn ht ha hR0 root j jgood cs) i).val=y i:=by
  let older:=IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root j jgood
  have HO :older.length≤(P).cap root+1+1:=by
    dsimp only [older,IntegralMixedMarkedRecordContinuation.oldCommands]
    rw [IntegralMixedCausalPlanBits.commands_length]
    exact IntegralMixedMarkedRecordContinuation.room_before hn ht ha hR0 root j jgood
  have HZ :∀i,((IntegralMixedFullHistoryScript.continueRun
      (reframe (run (initial P D root) older HO) (Q root)
        (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root))) cs hc).sampler.rows i).eval₂
          (Int.castRingHom ℝ) tuple=0:=by
    simpa only [older,state,IntegralMixedMarkedRecordContinuation.start,
      IntegralMixedCausalUnitContinuation.start,IntegralMixedMarkedRecordContinuation.oldCommands] using hz
  obtain ⟨u,y,hy,hu,hcol⟩:=IntegralMixedFramedFixedContinuation.tuple_append_observation
    (initial P D root) (Q root) (IntegralMixedStaticRecordPrefix.cap (Q root) (cap root)) older HO cs hc tuple HZ
  have HP :paddedPast (defaultInstruction P D root) ((D).rules root) (number n root+8+j+codes.length)=
      wrappedCommands hn ht ha hR0 root j jgood cs:=
    compiled_commands hn ht ha hR0 root j jgood codes hj hw cs hc HD
  have HE:=observation_eq (initial P D root) _ _
    (by rw [paddedPast_length];exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root
      (number n root+8+j+codes.length) (by omega)).trans (Nat.le_succ _))
    (by simp only [wrappedCommands,List.length_append,List.length_map];omega) HP
  exact ⟨u,y,hy,(congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots u) HE).mpr hu,hcol⟩

end LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
