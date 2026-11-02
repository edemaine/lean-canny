/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
/-! # Prepared-root frozen/free validity is a native flag, not level FP -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Valid {F : Inputs} (h r : (u : List Bool) → Fin (arity F u)) (root : List Bool) : Prop :=
  (pairFst (pairSnd root))[(h (pairFst root)).val]?.getD false = true ∧
    (pairFst (pairSnd root))[(r (pairFst root)).val]?.getD false = false
instance {F : Inputs} (h r : (u : List Bool) → Fin (arity F u)) (root : List Bool) : Decidable (Valid h r root) := inferInstanceAs (Decidable (_ ∧ _))

theorem valid_FP {F : Inputs} (hF : F.Access) (h r : (u : List Bool) → Fin (arity F u))
    (hh : BinaryFn (fun u => (h u).val)) (hr : BinaryFn (fun u => (r u).val)) : FPPred (Valid h r) := by
  have HW := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HH := FPPred.getBit HW ((FlatAffineExceptionalSelectorSpace.height_unary hF h hh).comp pairFst_mem_FP)
  have HR := FPPred.getBit HW ((FlatAffineExceptionalSelectorSpace.height_unary hF r hr).comp pairFst_mem_FP)
  have HN : FPPred (fun root => (pairFst (pairSnd root))[(r (pairFst root)).val]?.getD false = false) :=
    HR.not.of_iff (fun root => by dsimp only [Function.comp_apply]; cases (pairFst (pairSnd root))[(r (pairFst root)).val]?.getD false <;> simp)
  exact HH.and HN

theorem valid_prepare (F : Inputs) (h r : (u : List Bool) → Fin (arity F u)) (p : List Bool) :
    Valid h r (prepare F p) ↔ h (pairFst p) ∈ FlatAffineExceptionalOrderedRule.frozen F (pairFst p) ∧
      r (pairFst p) ∉ FlatAffineExceptionalOrderedRule.frozen F (pairFst p) := by
  have HH := congrArg₂ (fun (u w : List Bool) => w[(h u).val]?.getD false) (input_prepare F p) (mask_prepare F p)
  have HR := congrArg₂ (fun (u w : List Bool) => w[(r u).val]?.getD false) (input_prepare F p) (mask_prepare F p)
  unfold Valid
  rw [HH, HR, FrozenCoordinatePermutationBits.mask_get, FrozenCoordinatePermutationBits.mask_get]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]

theorem valid_separate_eq {F : Inputs} (h r : (u : List Bool) → Fin (arity F u)) (root : List Bool)
    (hv : Valid h r root) : separate (h (pairFst root)) (r (pairFst root)) = r (pairFst root) := by
  apply separate_eq
  intro he
  have HE := congrArg (fun i : Fin (arity F (pairFst root)) => (pairFst (pairSnd root))[i.val]?.getD false) he
  rw [hv.1, hv.2] at HE
  cases HE
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
