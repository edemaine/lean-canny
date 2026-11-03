/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalNaturalPoint
/-! # Literal old bank readback from one unchanged full joint tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (enumerate slotNumber)
open IntegralMixedFramedRunObservation (ofCommands)
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem denominator_cons {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (c : Instruction n B) (cs : List (Instruction n B))
    (hc : (c::cs).length≤S+1) (ht : cs.length≤S+1) (i : Fin cs.length) :
    (run x (c::cs) hc).bank.denominator i.succ=(run x cs ht).bank.denominator i :=
  IntegralMixedFullHistoryScript.step_denominator_succ
    (reframe (run x cs ht) c.source c.source_cap) (by simp only [List.length_cons] at hc;omega) c.command i

theorem point_cons {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (c : Instruction n B) (cs : List (Instruction n B))
    (hc : (c::cs).length≤S+1) (ht : cs.length≤S+1) (z : ℕ→ℝ) (i : Fin cs.length) :
    (ofCommands x (c::cs) hc).point z (i.val+1)=(ofCommands x cs ht).point z i.val :=by
  dsimp only [IntegralMixedFramedRunObservation.Data.point,ofCommands,
    IntegralMixedFramedBankObservation.Data.point,IntegralMixedFramedBankObservation.ofState]
  rw [dite_eq_left (show i.val+1<(c::cs).length by simp only [List.length_cons];omega),dite_eq_left i.isLt]
  change z (slotNumber (c::cs) (i.val+1))^
      UniformIntegralPowerSchedule.weights S (2^B) (cs.length+1) i.succ /
        ((run x (c::cs) hc).bank.denominator i.succ:ℝ)=_
  rw [denominator_cons x c cs hc ht i,UniformIntegralPowerSchedule.old]
  simp only [slotNumber,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]

theorem point_drop_one {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs : List (Instruction n B))
    (hc : cs.length≤S+1) (ht : (cs.drop 1).length≤S+1) (z : ℕ→ℝ) (i : Fin (cs.drop 1).length) :
    (ofCommands x (cs.drop 1) ht).point z i.val=(ofCommands x cs hc).point z (i.val+1) :=by
  cases cs with
  | nil=>exact Fin.elim0 i
  | cons c cs=>exact (point_cons x c cs hc ht z i).symm

theorem full_point (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) c w)
    (i : Fin (commands P D (key c)).length) :
    (ofCommands (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst (key c)))
      (commands P D (key c)) (((family P D H).birth_bound (key c)).trans (Nat.le_succ _))).point
      (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hpos c w hv) i.val=
        IntegralFramedPhysicalSquare.point P D H L F C hs key hpos c w hv i :=by
  rw [IntegralMixedFramedRunObservation.point_actual]
  change IntegralMixedCanonicalBankPoint.point _
      (fun j=>IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hpos c w hv
        (enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar j)).val) i=
    IntegralMixedCanonicalBankPoint.point _
      (fun j=>IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos c w hv
        (enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar j))) i
  congr 1
  funext j
  exact IntegralFramedPhysicalSquare.naturalPoint_at P D H L F C hs key hpos c w hv _
end LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
