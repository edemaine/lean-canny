/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalAdvisedBankScalarControls
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedLimitLabels
/-! # Actual original-bank limit-cut histories have derived scalar controls -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def limitBankDescription (P : Parameters) {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1) : Description P F :=
  limitDescription P S C (integerBase P S C base hW hroom)
    (fun root => by rw [integerBase_length]; exact hroom root)
    (integerBase_integer P S C base hW hroom)

theorem limit_bank_scalar_controls (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (S : FlatAffineExceptionalSuppliedRules.Source F) (hS : FlatAffineExceptionalSuppliedRules.Access S)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (S.input root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (S.input root) + 4 ≤ P.cap root + 1)
    (hl : ∀ root, (base.spatial root).leading = 1) :
    IntegralMixedFullScalarBits.Controls (parameters P S) (backend P (limitBankDescription P S C base hW hroom)) := by
  have HN : UnaryFn (fun root => ((integerBase P S C base hW hroom).rules root).length) :=
    ((FlatAffineExceptionalBankSource.births_unary hF).comp hS.input).of_eq (fun root => (integerBase_length P S C base hW hroom root).symm)
  exact scalar_controls P a hF (limitBankDescription P S C base hW hroom) hS HN
    (limitKind_access P a hF S hS C (integerBase P S C base hW hroom) _ _) hl

theorem advised_limit_bank_scalar_controls (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (h r : (u : List Bool) → Fin (arity F u))
    (hh : BinaryFn (fun u => (h u).val)) (hr : BinaryFn (fun u => (r u).val))
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P (FlatAffineExceptionalSuppliedAdvice.source F h r)))
    (hW : ∀ root, FlatAffineExceptionalBankSource.width F (pairFst root) ≤ P.width root)
    (hroom : ∀ root, FlatAffineExceptionalBankSource.births F (pairFst root) + 4 ≤ P.cap root + 1)
    (hl : ∀ root, (base.spatial root).leading = 1) :
    IntegralMixedFullScalarBits.Controls (parameters P (FlatAffineExceptionalSuppliedAdvice.source F h r))
      (backend P (limitBankDescription P (FlatAffineExceptionalSuppliedAdvice.source F h r) C base hW hroom)) :=
  limit_bank_scalar_controls P a hF (FlatAffineExceptionalSuppliedAdvice.source F h r)
    (FlatAffineExceptionalSuppliedAdvice.source_access hF h r hh hr) C base hW hroom hl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
