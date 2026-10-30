/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineEndpointFiniteLift
public import Mathlib.Tactic.FinCases

/-! # Original equations recovered from every joint endpoint tuple -/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineEndpointFiniteProjection
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def sample (F : Inputs) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) : ℝ :=
  z ⟨0, Nat.zero_lt_succ _⟩

def endpoint (F : Inputs) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) : ℝ :=
  z (FrozenAffineCopies.block (0 : Fin 1) (FlatAffineEndpointRows.zero F (pairFst s)))

def copy (F : Inputs) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ)
    (k : Fin 3) : Fin (count F (pairFst (pairFst s))) → ℝ :=
  z ∘ FrozenAffineCopies.block (0 : Fin 1) ∘ FrozenAffineCopies.block k

theorem sample_point (F : Inputs) (s : List Bool) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ) :
    sample F s (FlatAffineEndpointFiniteLift.point F s a t current left right) = t := rfl

theorem endpoint_point (F : Inputs) (s : List Bool) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ) :
    endpoint F s (FlatAffineEndpointFiniteLift.point F s a t current left right) = a := by
  unfold endpoint FlatAffineEndpointFiniteLift.point
  rw [FrozenAffineCopies.point_block]
  have hz : FlatAffineEndpointRows.zero F (pairFst s) = (0 : Fin (3 * count F (pairFst (pairFst s)) + 1)) := Fin.ext rfl
  rw [hz, FrozenAffineCopies.point_zero]

theorem copy_point (F : Inputs) (s : List Bool) (a t : ℝ)
    (current left right : Fin (count F (pairFst (pairFst s))) → ℝ) (k : Fin 3) :
    copy F s (FlatAffineEndpointFiniteLift.point F s a t current left right) k = ![current, left, right] k := by
  funext i
  simp only [copy, Function.comp_apply, FlatAffineEndpointFiniteLift.point, FrozenAffineCopies.point_block]

private theorem point_eta {n m : ℕ} {K : Type*} (z : Fin (m * n + 1) → K) :
    FrozenAffineCopies.point (z 0) (fun k i => z (FrozenAffineCopies.block k i)) = z := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  change z (FrozenAffineCopies.block (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2) = z j.succ
  rw [FrozenAffineCopies.block, Equiv.apply_symm_apply]

theorem reconstruct (F : Inputs) (s : List Bool) (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) :
    FlatAffineEndpointFiniteLift.point F s (endpoint F s z) (sample F s z)
      (copy F s z 0) (copy F s z 1) (copy F s z 2) = z := by
  have hi : FrozenAffineCopies.point (endpoint F s z) ![copy F s z 0, copy F s z 1, copy F s z 2] =
      z ∘ FrozenAffineCopies.block (0 : Fin 1) := by
    have he : ![copy F s z 0, copy F s z 1, copy F s z 2] =
        (fun k i => z (FrozenAffineCopies.block (0 : Fin 1) (FrozenAffineCopies.block k i))) := by
      funext k i
      fin_cases k <;> rfl
    rw [he]
    exact point_eta (z ∘ FrozenAffineCopies.block (0 : Fin 1))
  unfold FlatAffineEndpointFiniteLift.point
  rw [hi]
  have he : (fun _ : Fin 1 => z ∘ FrozenAffineCopies.block (0 : Fin 1)) =
      (fun k => z ∘ FrozenAffineCopies.block k) := by
    funext k
    congr 2
    exact Subsingleton.elim _ _
  rw [he]
  exact point_eta z

theorem equations (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ)
    (hz : ∀ i, (FlatAffineEndpointFiniteFrame.system F height s i).eval₂ (Int.castRingHom ℝ) z = 0) :
    SymbolicScaledSquarefree.scalarEvaluation (sample F s z) (FlatAffineEndpointFiniteFrame.retained F height (pairFst s)) = 0 ∧
    SymbolicScaledSquarefree.scalarEvaluation (endpoint F s z)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0 ∧
    ∀ k i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) (copy F s z k) =
      if i = height (pairFst (pairFst s)) then (if k = 0 then sample F s z else endpoint F s z) else 0 := by
  have H := (FrozenAffineCopies.zero_iff (Int.castRingHom ℝ)
    (FlatAffineEndpointPreparation.system F height (pairFst s)) (FlatAffineEndpointFiniteFrame.retained F height (pairFst s))
    (FlatAffineEndpointGram.active F height (pairFst s)) (fun _ : Fin 1 => true) z).mp hz
  refine ⟨H.1, ?_, ?_⟩
  · have h0 : (0 : Fin (3 * count F (pairFst (pairFst s)) + 1)) ≠
        FlatAffineEndpointGram.active F height (pairFst s) := by
      intro he
      have he' := congrArg Fin.val he
      change 0 = (finProdFinEquiv ((0 : Fin 3), height (pairFst (pairFst s)))).val + 1 at he'
      omega
    have he := H.2 (0 : Fin 1) 0
    have hz0 : FlatAffineEndpointRows.zero F (pairFst s) = (0 : Fin (3 * count F (pairFst (pairFst s)) + 1)) := Fin.ext rfl
    simp only [true_and, ite_eq_right h0] at he
    simpa only [FlatAffineEndpointPreparation.system, FrozenAffineCopies.system_zero,
      IndexedMultivariateRational.eval_parameter, Function.comp_apply, endpoint, hz0,
      SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom] using he
  · intro k i
    have he := H.2 (0 : Fin 1) (FrozenAffineCopies.block k i)
    change (FrozenAffineCopies.system _ _ _ _ (FrozenAffineCopies.block k i)).eval₂ _ _ = _ at he
    rw [FrozenAffineCopies.system_block, FrozenAffineCopies.row_eval] at he
    change (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) (copy F s z k) -
      (if FlatAffineEndpointPreparation.frozen k = true ∧ i = height (pairFst (pairFst s)) then endpoint F s z else 0) =
      (if true = true ∧ FrozenAffineCopies.block k i = FrozenAffineCopies.block (0 : Fin 3) (height (pairFst (pairFst s)))
        then sample F s z else 0) at he
    fin_cases k <;> by_cases hi : i = height (pairFst (pairFst s)) <;>
      simp [FlatAffineEndpointPreparation.frozen, FrozenAffineCopies.block_eq_iff, hi] at he ⊢ <;>
      first | exact he | exact sub_eq_zero.mp he

def prefixCount (F : Inputs) (s : List Bool) : ℕ := 2 * count F (pairFst (pairFst s)) + 2

theorem prefixCount_unary {F : Inputs} (h : F.Access) : UnaryFn (prefixCount F) :=
  ((UnaryFn.const 2).mul ((FlatAffineFullSourcePositive.count_unary h).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))).add (UnaryFn.const 2)

theorem prefixCount_le (F : Inputs) (s : List Bool) : prefixCount F s ≤ FlatAffineEndpointFiniteFrame.arity F s := by
  dsimp only [prefixCount, FlatAffineEndpointFiniteFrame.arity, FlatAffineEndpointRows.arity, FlatAffineEndpointRows.originalCount]
  omega

def slot (F : Inputs) (s : List Bool) (k : Fin 3) (i : Fin (count F (pairFst (pairFst s)))) :
    Fin (FlatAffineEndpointFiniteFrame.arity F s) :=
  FrozenAffineCopies.block (0 : Fin 1) (FrozenAffineCopies.block k i)

theorem slot_val (F : Inputs) (s : List Bool) (k : Fin 3) (i : Fin (count F (pairFst (pairFst s)))) :
    (slot F s k i).val = i.val + count F (pairFst (pairFst s)) * k.val + 2 := by
  change (i.val + count F (pairFst (pairFst s)) * k.val + 1) +
    (3 * count F (pairFst (pairFst s)) + 1) * 0 + 1 = _
  omega

theorem prefix_iff (F : Inputs) (s : List Bool) (z v : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ) :
    (∀ i, i.val < prefixCount F s → z i = v i) ↔
      sample F s z = sample F s v ∧ endpoint F s z = endpoint F s v ∧
        copy F s z 0 = copy F s v 0 ∧ copy F s z 1 = copy F s v 1 := by
  constructor
  · intro hp
    refine ⟨hp _ (by dsimp [prefixCount]; omega), hp _ (by change 1 < prefixCount F s; dsimp [prefixCount]; omega), ?_, ?_⟩
    · funext i
      apply hp (slot F s 0 i)
      rw [slot_val]
      dsimp only [prefixCount]
      have := i.isLt
      omega
    · funext i
      apply hp (slot F s 1 i)
      rw [slot_val]
      dsimp only [prefixCount]
      have := i.isLt
      omega
  · rintro ⟨ht, ha, hc, hl⟩ j hj
    by_cases h0 : j.val = 0
    · have he : j = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext h0
      subst j
      exact ht
    by_cases h1 : j.val = 1
    · have he : j = FrozenAffineCopies.block (0 : Fin 1) (FlatAffineEndpointRows.zero F (pairFst s)) := Fin.ext h1
      subst j
      exact ha
    by_cases hn : j.val < count F (pairFst (pairFst s)) + 2
    · let i : Fin (count F (pairFst (pairFst s))) := ⟨j.val - 2, by omega⟩
      have he : j = slot F s 0 i := by
        apply Fin.ext
        rw [slot_val]
        dsimp only [i]
        omega
      rw [he]
      exact congrFun hc i
    · let i : Fin (count F (pairFst (pairFst s))) :=
        ⟨j.val - count F (pairFst (pairFst s)) - 2, by dsimp only [prefixCount] at hj; omega⟩
      have he : j = slot F s 1 i := by
        apply Fin.ext
        rw [slot_val]
        dsimp only [i]
        omega
      rw [he]
      exact congrFun hl i

theorem prefix_point (F : Inputs) (s : List Bool) (a t : ℝ)
    (current left right other : Fin (count F (pairFst (pairFst s))) → ℝ) :
    ∀ i, i.val < prefixCount F s →
      FlatAffineEndpointFiniteLift.point F s a t current left right i =
        FlatAffineEndpointFiniteLift.point F s a t current left other i := by
  rw [prefix_iff]
  simp only [sample_point, endpoint_point, copy_point, Matrix.cons_val_zero, Matrix.cons_val_one, and_self]

end LeanCanny.Geometry.FlatAffineEndpointFiniteProjection
