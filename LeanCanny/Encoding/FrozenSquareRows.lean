/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareIntegerRows
public import LeanCanny.Algebra.FixedWidthBlockRowSpace
public import LeanCanny.Algebra.FrozenAffineCopies
public import LeanCanny.Algebra.UnivariateRowSpace

/-! # Native row access after retaining one algebraic height

Embed an original square system in one variable block, retain a native
univariate height equation, and subtract the height variable from one row.
Original row readers and the retained polynomial reader are both charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FrozenSquareRows
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open SquareIntegerRows (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def arity (F : Family) (u : List Bool) : ℕ := 1 * F.count u + 1
def zero (F : Family) (u : List Bool) : Fin (arity F u) := ⟨0, Nat.zero_lt_succ _⟩
theorem arity_unary {F : Family} (A : F.Access) : UnaryFn (arity F) :=
  ((UnaryFn.const 1).mul A.count).add (UnaryFn.const 1)

noncomputable def tail (F : Family) (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) : Fin (1 * F.count u) :=
  ⟨(row u).val - 1, by have := (row u).isLt; have := F.count_pos u; dsimp only [arity] at *; omega⟩
noncomputable def copy (F : Family) (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) : Fin 1 :=
  (finProdFinEquiv.symm (tail F row u)).1
noncomputable def localRow (F : Family) (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) : Fin (F.count u) :=
  (finProdFinEquiv.symm (tail F row u)).2

theorem localRow_unary {F : Family} (A : F.Access) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) : UnaryFn (fun u => (localRow F row u).val) :=
  (hr.sub (UnaryFn.const 1)).mod A.count

theorem block_fits (F : Family) (u : List Bool) : 1 + F.count u ≤ arity F u := by simp [arity, Nat.add_comm]

theorem block_eq (F : Family) (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    FrozenAffineCopies.block (copy F row u) = BlockRenameCoefficient.shift (F.count u) (arity F u) 1 (block_fits F u) := by
  funext i
  apply Fin.ext
  have hk : (copy F row u).val = 0 := by have := (copy F row u).isLt; omega
  change i.val + F.count u * (copy F row u).val + 1 = 1 + i.val
  rw [hk, Nat.mul_zero]
  omega

theorem originalEvaluator {F : Family} (A : F.Access) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthBlockRowBits.source F.count W (fun u => F.system u (localRow F row u)) modulus) :=
  SquareIntegerRows.rowEvaluator A pairFst pairFst_mem_FP (fun q => localRow F row (pairFst q))
    ((localRow_unary A row hr).comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)

theorem embeddedEvaluator {F : Family} (A : F.Access) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W (fun u => rename (FrozenAffineCopies.block (copy F row u))
      (F.system u (localRow F row u))) target modulus) := by
  have H := FixedWidthBlockRowBits.evaluator A.count (arity_unary A) (UnaryFn.const 1) hW
    (block_fits F) (fun u => F.system u (localRow F row u)) target modulus ht (originalEvaluator A row hr hW hm)
  refine H.congr (funext fun u => ?_)
  rw [FixedWidthRowBits.value, FixedWidthRowBits.value, block_eq]
  rfl

noncomputable def Frozen (F : Family) (height : (u : List Bool) → Fin (F.count u))
    (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) : Prop := localRow F row u = height u
noncomputable instance (F : Family) (height : (u : List Bool) → Fin (F.count u))
    (row : (u : List Bool) → Fin (arity F u)) : DecidablePred (Frozen F height row) := fun _ => inferInstanceAs (Decidable (_ = _))

theorem frozen_pred {F : Family} (A : F.Access) (height : (u : List Bool) → Fin (F.count u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) : FPPred (Frozen F height row) :=
  ((BinaryFn.ofUnary (localRow_unary A row hr)).eq (BinaryFn.ofUnary hh)).of_iff (fun _ => Fin.ext_iff.symm)

noncomputable def selectedCopy (F : Family) (height : (u : List Bool) → Fin (F.count u))
    (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) : MvPolynomial (Fin (arity F u)) ℤ :=
  FrozenAffineCopies.row (F.system u) (height u) (fun _ : Fin 1 => true) (copy F row u) (localRow F row u)

theorem copyEvaluator {F : Family} (A : F.Access) (height : (u : List Bool) → Fin (F.count u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W (selectedCopy F height row) target modulus) := by
  have V := FixedWidthRowBits.variable_evaluator (arity F) W (zero F) target modulus (arity_unary A) hW (UnaryFn.const 0) ht hm
  have G := FixedWidthRowBits.guarded_evaluator (arity F) W (fun u => X (zero F u)) target modulus
    _ (Frozen F height row) (frozen_pred A height hh row hr) V (fun _ _ => rfl)
  have E := FixedWidthRowBits.sub_evaluator (arity F) W _ _ target modulus hm (embeddedEvaluator A row hr hW ht hm) G
  refine E.congr (funext fun u => ?_)
  have hz : zero F u = (0 : Fin (1 * F.count u + 1)) := by apply Fin.ext; rfl
  simp only [FixedWidthRowBits.value, selectedCopy, FrozenAffineCopies.row, Frozen, true_and]
  rw [hz]

theorem selected_eq (F : Family) (height : (u : List Bool) → Fin (F.count u)) (E : List Bool → Polynomial ℤ)
    (row : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    FrozenAffineCopies.system (F.system u) (E u) (height u) (fun _ : Fin 1 => true) (row u) =
      if (row u).val = 0 then (E u).toMvPolynomial (zero F u) else selectedCopy F height row u := by
  by_cases hz : (row u).val = 0
  · have he : row u = zero F u := Fin.ext hz
    rw [ite_eq_left hz, he]
    rfl
  · rw [ite_eq_right hz]
    have he : (tail F row u).succ = row u := Fin.ext (by change (row u).val - 1 + 1 = (row u).val; omega)
    calc
      _ = FrozenAffineCopies.system (F.system u) (E u) (height u) (fun _ : Fin 1 => true) (tail F row u).succ := congrArg _ he.symm
      _ = _ := rfl

theorem evaluator {F : Family} (A : F.Access) (height : (u : List Bool) → Fin (F.count u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (u : List Bool) → Fin (arity F u))
    (hr : UnaryFn (fun u => (row u).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    (E : List Bool → Polynomial ℤ) (EP : SpaceFunction (PrimitivePairBits.coefficient E))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W (fun u => FrozenAffineCopies.system (F.system u) (E u)
      (height u) (fun _ : Fin 1 => true) (row u)) target modulus) := by
  have P := UnivariateRowBits.evaluator (arity_unary A) hW (zero F) (UnaryFn.const 0) E EP ht hm
  have H := FixedWidthRowBits.branch_evaluator (arity F) W _ _ target modulus (fun u => (row u).val = 0)
    ((BinaryFn.ofUnary hr).eq (BinaryFn.const 0)) P (copyEvaluator A height hh row hr hW ht hm)
  refine H.congr (funext fun u => ?_)
  rw [FixedWidthRowBits.value, FixedWidthRowBits.value, selected_eq]

end LeanCanny.Encoding.FrozenSquareRows
