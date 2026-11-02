/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalFramedNativePlanned
public import LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
/-! # Unit snapshots remove the noncut fallback bound premise

The actual unit-selector snapshot already bounds every selected noncut rule.
Thus the actual-bank evaluator needs only original script/default source
bounds, positive arithmetic growth and a positive row-node allowance.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedNative
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open FlatAffineExceptionalFramedIntegerPrelude (plan)
open scoped Classical

theorem planned_model_space_of_unit (P : Parameters) (a : Access P) (base : Plan P)
    {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (input : List Bool → List Bool) (hi : input∈FP)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1)
    (hno : ∀ root c, c∈later root → c.command.context≠0)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P (plan P base F C h input later hW hroom))
    (s : Body P (plan P base F C h input later hW hroom) H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P (plan P base F C h input later hW hroom) s.nodes s.factor s.seed)
    (hfactor : ∀ root, 1≤s.factor root) (hL : ∀ root, 1≤s.nodes root) :
    SpaceFunction (plannedMachine P a base hF C h hh input hi later hW hroom hno H s).model :=
  planned_model_space P a base hF C h hh input hi later hW hroom hno H s hs hfactor
    (IntegralMixedFramedUnitSourceBounds.fallback_bounds P _ H s.unit.writer s.unit.snapshot s.nodes s.seed hL)

end LeanCanny.Encoding.FlatAffineExceptionalFramedNative
