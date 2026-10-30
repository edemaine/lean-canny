/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointPreparation
public import LeanCanny.Algebra.FixedWidthBlockRowSpace
public import LeanCanny.Algebra.UnivariateRowSpace

/-! # Native integer coefficients of the actual frozen endpoint copies

Original tower rows are embedded in their selected variable block. The
computed exceptional-polynomial reader supplies the retained equation, and
native linear subtraction supplies the frozen-height constraints.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRows
open LeanCanny.Algebra LeanCanny.Computation MatrixPower MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def originalCount (F : Inputs) (r : List Bool) : ℕ := count F (pairFst r)
def arity (F : Inputs) (r : List Bool) : ℕ := 3 * originalCount F r + 1

def zero (F : Inputs) (r : List Bool) : Fin (arity F r) := ⟨0, Nat.zero_lt_succ _⟩

theorem originalCount_unary {F : Inputs} (h : F.Access) : UnaryFn (originalCount F) :=
  (FlatAffineFullSourcePositive.count_unary h).comp pairFst_mem_FP

theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (arity F) :=
  ((UnaryFn.const 3).mul (originalCount_unary h)).add (UnaryFn.const 1)

noncomputable def tail (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : Fin (3 * originalCount F r) :=
  ⟨(row r).val - 1, by have := (row r).isLt; have := FlatAffineFullSourcePositive.count_pos F (pairFst r); dsimp [arity, originalCount] at *; omega⟩

noncomputable def copy (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : Fin 3 :=
  (finProdFinEquiv.symm (tail F row r)).1

noncomputable def localRow (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : Fin (originalCount F r) :=
  (finProdFinEquiv.symm (tail F row r)).2

theorem copy_unary {F : Inputs} (h : F.Access) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) : UnaryFn (fun r => (copy F row r).val) :=
  (hr.sub (UnaryFn.const 1)).div (originalCount_unary h)

theorem localRow_unary {F : Inputs} (h : F.Access) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) : UnaryFn (fun r => (localRow F row r).val) :=
  (hr.sub (UnaryFn.const 1)).mod (originalCount_unary h)

noncomputable def offset (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : ℕ :=
  1 + originalCount F r * (copy F row r).val

theorem offset_unary {F : Inputs} (h : F.Access) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) : UnaryFn (offset F row) :=
  (UnaryFn.const 1).add ((originalCount_unary h).mul (copy_unary h row hr))

theorem block_fits (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) :
    offset F row r + originalCount F r ≤ arity F r := by
  have H := Nat.mul_le_mul_left (originalCount F r) (copy F row r).isLt
  change originalCount F r * ((copy F row r).val + 1) ≤ originalCount F r * 3 at H
  dsimp only [offset, arity]
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm _ 3] at H
  omega

theorem block_eq (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) :
    FrozenAffineCopies.block (copy F row r) =
      BlockRenameCoefficient.shift (originalCount F r) (arity F r) (offset F row r) (block_fits F row r) := by
  funext i
  apply Fin.ext
  change i.val + originalCount F r * (copy F row r).val + 1 =
    1 + originalCount F r * (copy F row r).val + i.val
  omega

theorem originalEvaluator {F : Inputs} (h : F.Access) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthBlockRowBits.source (originalCount F) W
      (fun r => FlatAffinePowerPositive.system F (pairFst r) (localRow F row r)) modulus) := by
  have hf := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have H := FlatAffinePowerPositive.evaluator (FlatAffineFullSourceContext.access h hf)
    (fun q => localRow F row (pairFst q)) ((localRow_unary h row hr).comp pairFst_mem_FP)
    (hW.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)
  refine H.congr (funext fun q => ?_)
  change residueBits (((FlatAffinePowerPositive.system (FlatAffineFullSourceContext.comp F (pairFst ∘ pairFst)) q
    (localRow F row (pairFst q))).coeff _) : ZMod _) = _
  rw [FlatAffinePowerPositive.system_comp]
  rfl

theorem embeddedEvaluator {F : Inputs} (h : F.Access) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W (fun r => rename (FrozenAffineCopies.block (copy F row r))
      (FlatAffinePowerPositive.system F (pairFst r) (localRow F row r))) target modulus) := by
  have H := FixedWidthBlockRowBits.evaluator (originalCount_unary h) (arity_unary h)
    (offset_unary h row hr) hW (block_fits F row)
    (fun r => FlatAffinePowerPositive.system F (pairFst r) (localRow F row r)) target modulus ht
    (originalEvaluator h row hr hW hm)
  refine H.congr (funext fun r => ?_)
  rw [FixedWidthRowBits.value, FixedWidthRowBits.value, block_eq]
  rfl

noncomputable def Frozen (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : Prop :=
  FlatAffineEndpointPreparation.frozen (copy F row r) = true ∧ localRow F row r = height (pairFst r)
noncomputable instance (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (row : (r : List Bool) → Fin (arity F r)) : DecidablePred (Frozen F height row) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem frozen_fppred {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) : FPPred (Frozen F height row) := by
  have hc := (BinaryFn.ofUnary (copy_unary h row hr)).eq (BinaryFn.const 0)
  have hl := (BinaryFn.ofUnary (localRow_unary h row hr)).eq (BinaryFn.ofUnary (hh.comp pairFst_mem_FP))
  exact (hc.not.and hl).of_iff (fun r => by
    simp only [Frozen, FlatAffineEndpointPreparation.frozen, decide_eq_true_eq, Fin.ext_iff])

noncomputable def selectedCopy (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) : MvPolynomial (Fin (arity F r)) ℤ :=
  FrozenAffineCopies.row (FlatAffinePowerPositive.system F (pairFst r)) (height (pairFst r))
    FlatAffineEndpointPreparation.frozen (copy F row r) (localRow F row r)

theorem copyEvaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W (selectedCopy F height row) target modulus) := by
  let zeroVar (r : List Bool) : Fin (arity F r) := ⟨0, Nat.zero_lt_succ _⟩
  have V := FixedWidthRowBits.variable_evaluator (arity F) W zeroVar target modulus
    (arity_unary h) hW (UnaryFn.const 0) ht hm
  have G := FixedWidthRowBits.guarded_evaluator (arity F) W (fun r => X (zeroVar r)) target modulus
    _ (Frozen F height row) (frozen_fppred h height hh row hr) V (fun _ _ => rfl)
  exact FixedWidthRowBits.sub_evaluator (arity F) W _ _ target modulus hm
    (embeddedEvaluator h row hr hW ht hm) G

lemma selected_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (E : List Bool → Polynomial ℤ)
    (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) :
    FrozenAffineCopies.system (FlatAffinePowerPositive.system F (pairFst r)) (E r)
      (height (pairFst r)) FlatAffineEndpointPreparation.frozen (row r) =
      if (row r).val = 0 then
        (E r).toMvPolynomial (zero F r)
      else selectedCopy F height row r := by
  by_cases hz : (row r).val = 0
  · have he : row r = zero F r := Fin.ext hz
    rw [ite_eq_left hz, he]
    rfl
  · rw [ite_eq_right hz]
    have he : (tail F row r).succ = row r := by
      apply Fin.ext
      change (row r).val - 1 + 1 = (row r).val
      omega
    calc
      _ = FrozenAffineCopies.system (FlatAffinePowerPositive.system F (pairFst r)) (E r)
          (height (pairFst r)) FlatAffineEndpointPreparation.frozen (tail F row r).succ := congrArg _ he.symm
      _ = _ := rfl

lemma selected_degree (F : Inputs) (row : (r : List Bool) → Fin (arity F r)) (r : List Bool) (e : ℕ) :
    FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F (pairFst r)) e (row r) =
      if (row r).val = 0 then e
      else FlatAffinePowerPositive.degree F (pairFst r) (localRow F row r) := by
  by_cases hz : (row r).val = 0
  · have he : row r = zero F r := Fin.ext hz
    rw [ite_eq_left hz, he]
    rfl
  · rw [ite_eq_right hz]
    have he : (tail F row r).succ = row r := Fin.ext (by
      change (row r).val - 1 + 1 = (row r).val
      omega)
    calc
      _ = FrozenAffineCopies.degrees (FlatAffinePowerPositive.degree F (pairFst r)) e (tail F row r).succ := congrArg _ he.symm
      _ = _ := rfl

theorem evaluatorWithRetained {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    (E : List Bool → Polynomial ℤ) (EP : SpaceFunction (PrimitivePairBits.coefficient E))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W
      (fun r => FrozenAffineCopies.system (FlatAffinePowerPositive.system F (pairFst r)) (E r)
        (height (pairFst r)) FlatAffineEndpointPreparation.frozen (row r)) target modulus) := by
  let zeroVar (r : List Bool) : Fin (arity F r) := ⟨0, Nat.zero_lt_succ _⟩
  have P := UnivariateRowBits.evaluator (arity_unary h) hW zeroVar (UnaryFn.const 0)
    E EP ht hm
  have H := FixedWidthRowBits.branch_evaluator (arity F) W _ _ target modulus
    (fun r => (row r).val = 0) ((BinaryFn.ofUnary hr).eq (BinaryFn.const 0))
    P (copyEvaluator h height hh row hr hW ht hm)
  refine H.congr (funext fun r => ?_)
  rw [FixedWidthRowBits.value, FixedWidthRowBits.value, selected_eq]
  rfl

theorem evaluator {F : Inputs} (h : F.Access) (height : (u : List Bool) → Fin (count F u))
    (hh : UnaryFn (fun u => (height u).val)) (row : (r : List Bool) → Fin (arity F r))
    (hr : UnaryFn (fun r => (row r).val)) {W : List Bool → ℕ} (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity F) W
      (fun r => FlatAffineEndpointPreparation.system F height r (row r)) target modulus) :=
  evaluatorWithRetained h height hh row hr hW _ (FlatAffineEndpointPreparation.coefficientEvaluator h height hh) ht hm

end LeanCanny.Encoding.FlatAffineEndpointRows
