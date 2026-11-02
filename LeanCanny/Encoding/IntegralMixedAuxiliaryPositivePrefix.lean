/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptySquareSample
public import LeanCanny.Algebra.IntegralMixedFramedTerminalPrefix

/-! # A standard positive saved prefix, including original dimension zero

The key requests n+1 births within the existing horizon. If the encoded script
has n records, commands_terminal identifies the extra birth with its existing
integer-X default. No extra record is serialized and no positivity promise is
needed by this sampler input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryPositivePrefix
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters
open scoped Classical

def key (n : List Bool→ℕ) (root : List Bool→List Bool) (u : List Bool) : List Bool :=
  IntegralMixedFramedHistoryFamilyBits.keyAt (root u) (n (root u)+1) []

theorem key_FP {n : List Bool→ℕ} (hn : UnaryFn n) {root : List Bool→List Bool} (hr : root∈FP) : key n root∈FP :=
  mem_FP_pair hr (mem_FP_pair (BinaryFn.ofUnary ((hn.comp hr).add (UnaryFn.const 1))).bits_mem_FP (constFn_mem_FP []))

theorem key_prefix (n : List Bool→ℕ) (t : List Bool→Term) (root : List Bool→List Bool) (u : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n root u)=n (root u)+1 :=
  IntegralMixedFramedHistoryFamilyBits.keyAt_prefix (parameters n t) (root u) (n (root u)+1) []
    (Nat.succ_le_succ (original_coordinates n t (root u)))

theorem key_positive (n : List Bool→ℕ) (t : List Bool→Term) (root : List Bool→List Bool) (u : List Bool) :
    0<IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) (key n root u) :=
  (Nat.zero_lt_succ _).trans_eq (key_prefix n t root u).symm

noncomputable def input {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool→List Bool) : SquareSampleInput.Inputs :=
  IntegralMixedAuxiliaryEmptyPlan.squareInput hn ht ha (key n root) (key_positive n t root)

private theorem count_prefix (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (source : List Bool→List Bool)
    (hpos : ∀ u,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (source u)) (u : List Bool) :
    (IntegralFramedCompleteSquare.input P D H L F C h source hpos).count u=
      IntegralMixedFramedHistoryFamilyBits.prefixLength P (source u) :=
  IntegralMixedFramedHistoryFamilyBits.family_birth P D H (source u)

theorem count_eq {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool→List Bool) (u : List Bool) : (input hn ht ha root).count u=n (root u)+1 :=
  (count_prefix (parameters n t) (IntegralMixedAuxiliaryEmptyPlan.plan hn ht ha)
    (IntegralMixedAuxiliaryEmptyPlan.data hn ht ha) (fun _=>1) (IntegralMixedAuxiliarySchedule.factor n t)
    (IntegralMixedAuxiliarySchedule.seed n t) (IntegralMixedAuxiliaryEmptyPlan.familyInputs hn ht ha) (key n root)
    (fun v=>(key_positive n t root v).trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth (parameters n t)
      (IntegralMixedAuxiliaryEmptyPlan.plan hn ht ha) (IntegralMixedAuxiliaryEmptyPlan.data hn ht ha) (key n root v)).symm) u).trans
      (key_prefix n t root u)

theorem complete {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool→List Bool) : SquareSampleComplete.Complete (input hn ht ha root) :=
  IntegralMixedAuxiliaryEmptyPlan.square_complete hn ht ha (key n root) (key_positive n t root)

theorem access {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool→List Bool) (hr : root∈FP)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha root))) : (input hn ht ha root).Access :=
  IntegralMixedAuxiliaryEmptyPlan.square_access hn ht ha (key n root) (key_FP hn hr) (key_positive n t root) ER

theorem count_evaluator {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun root=>(t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool→List Bool) (hr : root∈FP)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha root))) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (input hn ht ha root) u)) :=
  SquareSampleComplete.count_evaluator (access hn ht ha root hr ER) (complete hn ht ha root)

end LeanCanny.Encoding.IntegralMixedAuxiliaryPositivePrefix
