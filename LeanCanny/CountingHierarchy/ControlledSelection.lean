/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.CountingHierarchy.ModularArithmetic

/-! # Uniform native choices and subtraction of controlled families -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P Q : (w : α) → MvPolynomial (Fin (n w)) ℤ}

noncomputable def select (C : Controlled P enc a) (b : α → Bool)
    (hb : ComputableInPolyTime b enc encBool) :
    Controlled (fun w => if b w then P w else 0) enc a where
  arity_computable := C.arity_computable
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := by cases b w <;> simp only [Bool.false_eq_true, ↓reduceIte, totalDegree_zero, Nat.zero_le, C.degree_le]
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := by cases b w <;> simp only [Bool.false_eq_true, ↓reduceIte, Algebra.MvMass.zero, Nat.zero_le, C.mass_le]
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate q := if b q.1 then C.evaluate q else 0
  evaluate_mem := CountingFunction.ite
    (CountingFunction.of_polyTime (hb.comp (ComputableInPolyTime.fst _ _)))
    C.evaluate_mem (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))
  evaluate_eq w p z hp hc := by
    cases b w <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [evaluation, MvPolynomial.eval₂_zero, ZMod.val_zero]
    · exact C.evaluate_eq w p z hp hc

noncomputable def neg (C : Controlled P enc a) : Controlled (fun w => -P w) enc a where
  arity_computable := C.arity_computable
  degreeBound := C.degreeBound
  degree_computable := C.degree_computable
  degree_le w := by rw [MvPolynomial.totalDegree_neg]; exact C.degree_le w
  massExponent := C.massExponent
  mass_computable := C.mass_computable
  mass_le w := by rw [Algebra.MvMass.neg]; exact C.mass_le w
  cutoff := C.cutoff
  cutoff_computable := C.cutoff_computable
  evaluate q := modularSub q.2.1 0 (C.evaluate q)
  evaluate_mem := modularSub_mem (CountingFunction.of_polyTime (by fun_prop))
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 0)) C.evaluate_mem
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    have h : (modularSub p 0 (C.evaluate (w, p, z)) : ZMod p) =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
          (fun i : Fin (n w) => (z[i.val]?.getD 0 : ZMod p)) (-P w) := by
      rw [modularSub_cast hp.pos, C.evaluate_eq w p z hp hc]
      simp only [Nat.cast_zero, zero_sub, evaluation, ZMod.natCast_zmod_val, MvPolynomial.eval₂_neg]
    simpa only [modularSub, ZMod.val_natCast, Nat.mod_mod, evaluation] using congrArg ZMod.val h

noncomputable def sub (C : Controlled P enc a) (D : Controlled Q enc a) :
    Controlled (fun w => P w - Q w) enc a where
  arity_computable := C.arity_computable
  degreeBound w := max (C.degreeBound w) (D.degreeBound w)
  degree_computable := ComputableInPolyTime.binary_max' C.degree_computable D.degree_computable
  degree_le w := (MvPolynomial.totalDegree_sub _ _).trans (max_le_max (C.degree_le w) (D.degree_le w))
  massExponent w := C.massExponent w + D.massExponent w + 1
  mass_computable := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' C.mass_computable D.mass_computable) (.const 1)
  mass_le w := by
    apply (Algebra.MvMass.sub_le _ _).trans
    apply (Nat.add_le_add (C.mass_le w) (D.mass_le w)).trans
    have hp : 2 ^ C.massExponent w ≤ 2 ^ (C.massExponent w + D.massExponent w) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hq : 2 ^ D.massExponent w ≤ 2 ^ (C.massExponent w + D.massExponent w) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ]
    omega
  cutoff w := max (C.cutoff w) (D.cutoff w)
  cutoff_computable := ComputableInPolyTime.binary_max' C.cutoff_computable D.cutoff_computable
  evaluate q := modularSub q.2.1 (C.evaluate q) (D.evaluate q)
  evaluate_mem := modularSub_mem (CountingFunction.of_polyTime (by fun_prop)) C.evaluate_mem D.evaluate_mem
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    have h : (modularSub p (C.evaluate (w, p, z)) (D.evaluate (w, p, z)) : ZMod p) =
        MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
          (fun i : Fin (n w) => (z[i.val]?.getD 0 : ZMod p)) (P w - Q w) := by
      rw [modularSub_cast hp.pos, C.evaluate_eq w p z hp ((le_max_left _ _).trans_lt hc),
        D.evaluate_eq w p z hp ((le_max_right _ _).trans_lt hc)]
      simp only [evaluation, ZMod.natCast_zmod_val, MvPolynomial.eval₂_sub]
    simpa only [modularSub, ZMod.val_natCast, Nat.mod_mod, evaluation] using congrArg ZMod.val h

end LeanCanny.CountingHierarchy.Controlled
