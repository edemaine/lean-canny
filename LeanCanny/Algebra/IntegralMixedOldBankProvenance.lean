/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryPrefix
public import LeanCanny.Algebra.IntegralMixedOldBankCofactor
/-! # Literal producer origins and fresh source keys of old-bank requests

The semantic producer labels below describe the actual creating command.
A native input codec must still read those immutable command fields. No
computability claim for the interpreted state or its leading is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Command.context {n B : ℕ} {P : SpatialSource n} : Command P B → ℕ
  | .integer .. => 0
  | .critical _ => 1
  | .cut _ (.coordinate ..) .. => 2
  | .cut _ (.squarefree ..) .. => 3
  | .cut _ (.value ..) .. => 4

def Command.coordinate {n B : ℕ} {P : SpatialSource n} : Command P B → ℕ
  | .integer .. => 0
  | .critical r => r.coordinate % (n - r.offset.val + 1)
  | .cut _ (.coordinate j _) .. => j.val
  | .cut _ (.squarefree j _) .. => j.val
  | .cut _ (.value i _) .. => i.val

theorem Command.context_le {n B : ℕ} {P : SpatialSource n} (c : Command P B) : c.context ≤ 4 := by
  cases c with
  | integer => norm_num [Command.context]
  | critical => norm_num [Command.context]
  | cut r k d ha hd => cases k <;> norm_num [Command.context]

theorem Command.coordinate_le {n B : ℕ} {P : SpatialSource n} (c : Command P B) : c.coordinate ≤ n := by
  cases c with
  | integer => exact Nat.zero_le _
  | critical r =>
    have H := Nat.mod_lt r.coordinate (Nat.succ_pos (n - r.offset.val))
    change r.coordinate % (n - r.offset.val + 1) < n - r.offset.val + 1 at H
    dsimp only [Command.coordinate]
    omega
  | cut r k d ha hd => cases k with
    | coordinate j _ => have H := j.isLt; dsimp only [Command.coordinate]; omega
    | squarefree j _ => have H := j.isLt; dsimp only [Command.coordinate]; omega
    | value i _ => have H := i.isLt; dsimp only [Command.coordinate]; omega

theorem retained_cut_leading {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Command P B)) (h : cs.length ≤ S + 1) (i : Fin cs.length)
    (r : IntegralMixedCriticalSweep.Rule n) (k : IntegralMixedRelativeCuts.Kind P r) (d : ℕ) (ha : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree) (hd : d ≤ 2 ^ B)
    (hc : chosen cs i = .cut r k d ha hd) : (run initial cs h).bank.denominator i =
      normalizedScalarLeading (birthState initial cs h i)
        (IntegralMixedCutMatrix.raw (birthState initial cs h i) (older_bound cs h i) r k d) d := by
  rw [retained_leading, hc]
  rfl

theorem padded_producer_birth {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (m : ℕ)
    (i : Fin (paddedPast cs m).length) : (older (paddedPast cs m) i).length = m - 1 - i.val := by
  rw [older_length]
  exact congrArg (fun length : ℕ => length - 1 - i.val) (paddedPast_length cs m)

theorem padded_producer_command {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (m : ℕ)
    (i : Fin (paddedPast cs m).length) : chronological (paddedPast cs m) (m - 1 - i.val) = some (chosen (paddedPast cs m) i) := by
  rw [← padded_producer_birth cs m i]
  exact chronological_older _ i
end LeanCanny.Algebra.IntegralMixedFullHistoryScript

namespace LeanCanny.Algebra.IntegralMixedOldBankCofactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

theorem writer_packet_source_birth (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < count P F q) :
    F.birth (IntegralMixedVirtualTaskBits.saved P (writer P R (packet P F q i))) = count P F q - 1 - i :=
  (g.birth _).trans (writer_packet_birth P F g R q i hi)

theorem writer_packet_saved (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < count P F q)
    (hc : R.context (packet P F q i) ≤ numericCap P (RankedHistoryTask.root q)) :
    IntegralMixedVirtualTaskBits.saved P (writer P R (packet P F q i)) =
      pair (RankedHistoryTask.root q) (pair (BinaryNatCode.encode (count P F q - 1 - i)) (BinaryNatCode.encode (R.context (packet P F q i)))) := by
  have HR : RankedHistoryTask.root (writer P R (packet P F q i)) = RankedHistoryTask.root q := by
    rw [writer_root]
    exact pairFst_pair _ _ |> congrArg RankedHistoryTask.root
  have HC : get P .slot15 (writer P R (packet P F q i)) = R.context (packet P F q i) := by
    apply IntegralMixedRoutineContextQuery.query_context
    simpa only [packet, pairFst_pair] using hc
  simp only [IntegralMixedVirtualTaskBits.saved, HR, writer_packet_birth P F g R q i hi, HC]

theorem writer_packet_coordinate (P : Parameters) (F : Family) (R : Routing) (q : List Bool) (i : ℕ)
    (hc : R.coordinate (packet P F q i) ≤ numericCap P (RankedHistoryTask.root q)) :
    get P .slot13 (writer P R (packet P F q i)) = R.coordinate (packet P F q i) := by
  apply IntegralMixedRoutineContextQuery.query_coordinate
  simpa only [packet, pairFst_pair] using hc
end LeanCanny.Algebra.IntegralMixedOldBankCofactorBits
