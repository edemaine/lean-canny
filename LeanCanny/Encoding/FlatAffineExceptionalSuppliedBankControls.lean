/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedControls
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedCoordinateLabels
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
/-! # Actual original-bank advice roots have constructed scalar/header controls

The initial integer commands are the actual exceptional parent-bank
polynomials. Later commands decode only supplied masks and cut labels.
All metadata is total on arbitrary roots, while original level/direction
access remains charged Space. There is no coefficient/height cell premise.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def integerBase (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1) :
    IntegralMixedFullHistoryFamilyBits.Data (parameters P S) :=
  FlatAffineExceptionalIntegerProducer.data (parameters P S) base F C S.height S.input (fun _ => []) hW
    (fun root => by have H := hroom root; simpa only [List.length_nil, Nat.zero_add, parameters] using (by omega : FlatAffineExceptionalBankSource.births F (S.input root) + 2 ≤ P.cap root + 1))

theorem integerBase_length (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1) (root : List Bool) :
    ((integerBase P S C base hW hroom).rules root).length = FlatAffineExceptionalBankSource.births F (S.input root) := by
  change (FlatAffineExceptionalIntegerCommands.commands _ _ F C S.height (S.input root) (hW root)).length = _
  exact FlatAffineExceptionalIntegerCommands.length_commands _ _ F C S.height (S.input root) (hW root)

theorem integerBase_integer (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1)
    (root : List Bool) (c : IntegralMixedFullHistoryScript.Command ((integerBase P S C base hW hroom).spatial root) ((parameters P S).width root))
    (hc : c ∈ (integerBase P S C base hW hroom).rules root) : IsInteger c := by
  change c ∈ List.ofFn (FlatAffineExceptionalIntegerCommands.command _ _ F C S.height (S.input root) (hW root)) at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  trivial

noncomputable def bankDescription (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1) : Description P F :=
  coordinateDescription P S C (integerBase P S C base hW hroom)
    (fun root => by rw [integerBase_length]; exact hroom root)
    (integerBase_integer P S C base hW hroom)

theorem bank_scalar_controls (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (S : FlatAffineExceptionalSuppliedRules.Source F) (hS : FlatAffineExceptionalSuppliedRules.Access S)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1)
    (hl : ∀ root, (base.spatial root).leading = 1) :
    IntegralMixedFullScalarBits.Controls (parameters P S) (backend P (bankDescription P S C base hW hroom)) := by
  have HN : UnaryFn (fun root => ((integerBase P S C base hW hroom).rules root).length) :=
    ((FlatAffineExceptionalBankSource.births_unary hF).comp hS.input).of_eq (fun root => (integerBase_length P S C base hW hroom root).symm)
  exact scalar_controls P a hF (bankDescription P S C base hW hroom) hS HN
    (coordinateKind_access P a hF S hS C (integerBase P S C base hW hroom) _ _) hl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
