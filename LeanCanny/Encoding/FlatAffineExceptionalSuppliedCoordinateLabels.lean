/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedHeaders
/-! # Cut labels decode to total bounded coordinate commands

The three labels are original binary words, not algebraic queries. Their
finite indices are reduced modulo the original degree bounds, and the written
truncation degree is clipped to the original auxiliary cap.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def labels (root : List Bool) := pairSnd (pairSnd root)
def rawCoordinate (root : List Bool) := Nat.fromBitsLE (pairFst (labels root))
def rawChoice (root : List Bool) := Nat.fromBitsLE (pairFst (pairSnd (labels root)))
def rawDegree (root : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd (labels root)))
theorem labels_FP : labels ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem rawCoordinate_binary : BinaryFn rawCoordinate := BinaryFn.fromBits (mem_FP_comp (f := labels) (g := pairFst) labels_FP pairFst_mem_FP)
theorem rawChoice_binary : BinaryFn rawChoice := BinaryFn.fromBits (mem_FP_comp (f := labels) (g := fun w => pairFst (pairSnd w)) labels_FP (mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP))
theorem rawDegree_binary : BinaryFn rawDegree := BinaryFn.fromBits (mem_FP_comp (f := labels) (g := fun w => pairSnd (pairSnd w)) labels_FP (mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP))

noncomputable def freeCount {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F) (root : List Bool) :=
  F.source.dim (S.input root) + 3 - (FlatAffineExceptionalSuppliedRules.critical S root).offset.val + 1

theorem freeCount_unary {F : Inputs} (hF : F.Access) (S : FlatAffineExceptionalSuppliedRules.Source F)
    (hS : FlatAffineExceptionalSuppliedRules.Access S) : UnaryFn (freeCount S) := by
  have HA : UnaryFn (fun root => F.source.dim (S.input root) + 3) :=
    (((FlatAffineFullSourceTower.arity_unary hF).comp hS.input).sub (UnaryFn.const 1)).of_eq (fun root => by unfold arity; omega)
  have HO : UnaryFn (fun root => (FlatAffineExceptionalSuppliedRules.critical S root).offset.val) :=
    (FlatAffineExceptionalSuppliedRules.offset_unary hF S hS).of_eq (fun root => FlatAffineExceptionalSuppliedRules.offset_eq S root)
  exact (HA.sub HO).add (UnaryFn.const 1)

noncomputable def coordinateKind (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S)) (root : List Bool) :
    IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root) :=
  .coordinate ⟨rawCoordinate root % freeCount S root, Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨rawChoice root % IntegralMixedCoordinateTrailing.ChoiceBound (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root),
      Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def coordinateDegree (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S)) (root : List Bool) :=
  min (rawDegree root) (IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P S).ambient root + 1) (base.spatial root).degree)

noncomputable def coordinateDescription (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) : Description P F where
  source := S
  cone := C
  base := base
  kind := coordinateKind P S C base
  degree := coordinateDegree P S base
  degree_bound _ := min_le_right _ _
  room := room
  integers := hi

theorem coordinateKind_access (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (S : FlatAffineExceptionalSuppliedRules.Source F) (hS : FlatAffineExceptionalSuppliedRules.Access S)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) : KindAccess P (coordinateDescription P S C base room hi) := by
  have HD : BinaryFn (fun root => (base.spatial root).degree) := a.degree.of_eq (fun root => (base.degree_eq root).symm)
  have HC : BinaryFn (fun root => IntegralMixedCoordinateTrailing.ChoiceBound (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root)) :=
    (PurePowerReductionBounds.dimension_binary (freeCount_unary hF S hS) HD).add (BinaryFn.const 1)
  have HA : BinaryFn (fun root => IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P S).ambient root + 1) (base.spatial root).degree) :=
    IntegralMixedExceptionalBounds.auxiliaryCap_binary ((parameters_access P a hF S hS).ambient.add (UnaryFn.const 1)) HD
  exact { context := BinaryFn.const 2
          coordinate := rawCoordinate_binary.mod (BinaryFn.ofUnary (freeCount_unary hF S hS))
          choice := rawChoice_binary.mod HC
          rawTag := BinaryFn.const 2
          degree := (BinaryFn.ite (rawDegree_binary.le HA) rawDegree_binary HA).of_eq (fun root => Nat.min_def.symm) }
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
