/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedRuleMetadata
/-! # A total advice-root decoder reserves distinct coordinates natively

A prepared root records the original input, its Space-computed flag mask,
and arbitrary original cut labels. Invalid supplied masks still define total
rules; agreement with genuine geometry is restricted to produced roots.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def separate {N : ℕ} (h r : Fin N) : Fin N :=
  if r = h then ⟨(h.val + 1) % N, Nat.mod_lt _ (by have HH := h.isLt; omega)⟩ else r

theorem separate_eq {N : ℕ} (h r : Fin N) (hr : r ≠ h) : separate h r = r := by rw [separate, ite_eq_right hr]

theorem separate_ne {N : ℕ} (h r : Fin N) (hN : 1 < N) : separate h r ≠ h := by
  by_cases hr : r = h
  · rw [separate, ite_eq_left hr]
    intro he
    have HV := congrArg Fin.val he
    change (h.val + 1) % N = h.val at HV
    have HH := h.isLt
    by_cases ht : h.val + 1 < N
    · rw [Nat.mod_eq_of_lt ht] at HV
      omega
    · have HN : h.val + 1 = N := by omega
      rw [HN, Nat.mod_self] at HV
      omega
  · rw [separate_eq h r hr]
    exact hr

theorem separate_binary {F : Inputs} (hF : F.Access) (h r : (u : List Bool) → Fin (arity F u))
    (hh : BinaryFn (fun u => (h u).val)) (hr : BinaryFn (fun u => (r u).val)) :
    BinaryFn (fun u => (separate (h u) (r u)).val) := by
  have H := BinaryFn.ite (hr.eq hh) ((hh.add (BinaryFn.const 1)).mod (BinaryFn.ofUnary (FlatAffineFullSourceTower.arity_unary hF))) hr
  apply H.of_eq
  intro u
  by_cases he : r u = h u
  · simp [separate, he]
  · have HV : (r u).val ≠ (h u).val := fun hv => he (Fin.ext hv)
    simp only [separate, he, ite_false, HV]

noncomputable def source (F : Inputs) (h r : (u : List Bool) → Fin (arity F u)) : FlatAffineExceptionalSuppliedRules.Source F where
  input := pairFst
  height := h
  free u := separate (h u) (r u)
  free_ne_height u := separate_ne _ _ (by unfold arity; omega)
  mask q := pairFst (pairSnd q)

theorem source_access {F : Inputs} (hF : F.Access) (h r : (u : List Bool) → Fin (arity F u))
    (hh : BinaryFn (fun u => (h u).val)) (hr : BinaryFn (fun u => (r u).val)) : FlatAffineExceptionalSuppliedRules.Access (source F h r) :=
  ⟨pairFst_mem_FP, hh, separate_binary hF h r hh hr, mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP⟩

noncomputable def prepare (F : Inputs) (p : List Bool) := pair (pairFst p)
  (pair (FlatAffineExceptionalSelectorSpace.maskWord F pairFst p) (pairSnd p))

theorem prepare_space {F : Inputs} (hF : F.Access) : SpaceFunction (prepare F) :=
  (SpaceFunction.ofFP _ pairFst_mem_FP).pairOutputs
    ((FlatAffineExceptionalSelectorSpace.maskWord_space hF pairFst pairFst_mem_FP).pairOutputs (SpaceFunction.ofFP _ pairSnd_mem_FP))

theorem prepare_length (F : Inputs) (p : List Bool) : (prepare F p).length =
    2 * (pairFst p).length + 2 * arity F (pairFst p) + 4 + (pairSnd p).length := by
  rw [prepare, pair_length, pair_length]
  simp only [FlatAffineExceptionalSelectorSpace.maskWord, List.length_map, List.length_range]
  omega

theorem prepare_length_unary {F : Inputs} (hF : F.Access) : UnaryFn (fun p => (prepare F p).length) :=
  ((((UnaryFn.const 2).mul (UnaryFn.length pairFst_mem_FP)).add
      ((UnaryFn.const 2).mul ((FlatAffineFullSourceTower.arity_unary hF).comp pairFst_mem_FP))).add
        (UnaryFn.const 4)).add (UnaryFn.length pairSnd_mem_FP) |>.of_eq (fun p => (prepare_length F p).symm)

theorem input_prepare (F : Inputs) (p : List Bool) : pairFst (prepare F p) = pairFst p := pairFst_pair _ _
theorem mask_prepare (F : Inputs) (p : List Bool) : pairFst (pairSnd (prepare F p)) =
    FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F (pairFst p)) := by
  rw [prepare, pairSnd_pair, pairFst_pair, FlatAffineExceptionalSelectorSpace.maskWord_eq]
  rfl
theorem labels_prepare (F : Inputs) (p : List Bool) : pairSnd (pairSnd (prepare F p)) = pairSnd p := by
  rw [prepare, pairSnd_pair, pairSnd_pair]

theorem frozen_prepare (F : Inputs) (h r : (u : List Bool) → Fin (arity F u)) (p : List Bool)
    (hh : h (pairFst p) ∈ FlatAffineExceptionalOrderedRule.frozen F (pairFst p))
    (hr : r (pairFst p) ∉ FlatAffineExceptionalOrderedRule.frozen F (pairFst p)) :
    HEq (FlatAffineExceptionalSuppliedRules.frozen (source F h r) (prepare F p)) (FlatAffineExceptionalOrderedRule.frozen F (pairFst p)) := by
  have HN : r (pairFst p) ≠ h (pairFst p) := fun he => hr (he.symm ▸ hh)
  change HEq (SuppliedFrozenMaskBits.pinned (pairFst (pairSnd (prepare F p)))
    (h (pairFst (prepare F p))) (separate (h (pairFst (prepare F p))) (r (pairFst (prepare F p))))) _
  rw [input_prepare, mask_prepare, separate_eq _ _ HN, SuppliedFrozenMaskBits.pinned_original _ _ _ hh hr]
theorem critical_prepare (F : Inputs) (h r : (u : List Bool) → Fin (arity F u)) (p : List Bool)
    (hh : h (pairFst (prepare F p)) ∈ FlatAffineExceptionalOrderedRule.frozen F (pairFst (prepare F p)))
    (hr : r (pairFst (prepare F p)) ∉ FlatAffineExceptionalOrderedRule.frozen F (pairFst (prepare F p))) :
    FlatAffineExceptionalSuppliedRules.critical (source F h r) (prepare F p) =
      FlatAffineExceptionalOrderedRule.rule F h (pairFst (prepare F p)) (r (pairFst (prepare F p))) hr := by
  have HN : r (pairFst (prepare F p)) ≠ h (pairFst (prepare F p)) := fun he => hr (he.symm ▸ hh)
  have HW : (source F h r).mask (prepare F p) = FrozenCoordinatePermutationBits.mask
      (FlatAffineExceptionalOrderedRule.frozen F ((source F h r).input (prepare F p))) :=
    (mask_prepare F p).trans (congrArg (fun u => FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F u)) (input_prepare F p).symm)
  have HF : (source F h r).free ((source F h r).input (prepare F p)) ∉
      FlatAffineExceptionalOrderedRule.frozen F ((source F h r).input (prepare F p)) := by
    simpa only [source, separate_eq _ _ HN] using hr
  have H := FlatAffineExceptionalSuppliedRules.critical_original (source F h r) (prepare F p) HW hh HF
  simpa only [source, separate_eq _ _ HN] using H

theorem coarse_prepare (F : Inputs) (h r : (u : List Bool) → Fin (arity F u)) (p : List Bool)
    (hh : h (pairFst (prepare F p)) ∈ FlatAffineExceptionalOrderedRule.frozen F (pairFst (prepare F p)))
    (hr : r (pairFst (prepare F p)) ∉ FlatAffineExceptionalOrderedRule.frozen F (pairFst (prepare F p))) :
    FlatAffineExceptionalSuppliedRules.coarse (source F h r) (prepare F p) =
      FlatAffineExceptionalCoarseRule.rule F h (pairFst (prepare F p)) := by
  have HN : r (pairFst (prepare F p)) ≠ h (pairFst (prepare F p)) := fun he => hr (he.symm ▸ hh)
  have HW : (source F h r).mask (prepare F p) = FrozenCoordinatePermutationBits.mask
      (FlatAffineExceptionalOrderedRule.frozen F ((source F h r).input (prepare F p))) :=
    (mask_prepare F p).trans (congrArg (fun u => FrozenCoordinatePermutationBits.mask (FlatAffineExceptionalOrderedRule.frozen F u)) (input_prepare F p).symm)
  have HF : (source F h r).free ((source F h r).input (prepare F p)) ∉
      FlatAffineExceptionalOrderedRule.frozen F ((source F h r).input (prepare F p)) := by
    simpa only [source, separate_eq _ _ HN] using hr
  exact FlatAffineExceptionalSuppliedRules.coarse_original (source F h r) (prepare F p) HW hh HF

end LeanCanny.Encoding.FlatAffineExceptionalSuppliedAdvice
