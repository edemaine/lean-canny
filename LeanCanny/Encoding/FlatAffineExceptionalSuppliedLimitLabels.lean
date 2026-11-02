/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedCoordinateLabels
/-! # Limit-coordinate cut labels retain script context 2 and raw tag 5 -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def limitKind (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S)) (root : List Bool) :
    IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root) :=
  .limitCoordinate ⟨rawCoordinate root % freeCount S root, Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨rawChoice root % IntegralMixedLimitCoordinate.ChoiceBound (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root),
      Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def limitDescription (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) : Description P F :=
  { coordinateDescription P S C base room hi with kind := limitKind P S C base }

theorem limitKind_access (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (S : FlatAffineExceptionalSuppliedRules.Source F) (hS : FlatAffineExceptionalSuppliedRules.Access S)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) : KindAccess P (limitDescription P S C base room hi) := by
  have H := coordinateKind_access P a hF S hS C base room hi
  exact { context := H.context
          coordinate := H.coordinate
          choice := H.choice
          rawTag := BinaryFn.const 5
          degree := H.degree }

theorem limit_description_context (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) (root : List Bool) :
    IntegralMixedCommandHeaderBits.kindContext ((limitDescription P S C base room hi).kind root) = 2 := rfl

theorem limit_description_rawTag (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1)
    (hi : ∀ root c, c ∈ base.rules root → IsInteger c) (root : List Bool) :
    IntegralMixedCommandHeaderBits.kindRawTag ((limitDescription P S C base room hi).kind root) = 5 := rfl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
