/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Binary addressed coordinates, with zero outside the variable block -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def optionalCoordinate (n i : ℕ) : MvPolynomial (Fin n) ℤ :=
  if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0

namespace Controlled

noncomputable def optionalCoordinate {α : Type} {n i : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hi : ComputableInPolyTime i enc encNat) :
    Controlled (fun w => LeanCanny.CountingHierarchy.optionalCoordinate (n w) (i w)) enc a where
  arity_computable := hn
  degreeBound _ := 1
  degree_computable := .const 1
  degree_le w := by unfold LeanCanny.CountingHierarchy.optionalCoordinate; split_ifs <;> simp
  massExponent _ := 0
  mass_computable := .const 0
  mass_le w := by unfold LeanCanny.CountingHierarchy.optionalCoordinate; split_ifs <;> simp
  cutoff _ := 0
  cutoff_computable := .const 0
  evaluate q := (if i q.1 < n q.1 then q.2.2[i q.1]?.getD 0 else 0) % q.2.1
  evaluate_mem := by
    apply CountingFunction.of_polyTime
    have hf := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    have hin := hi.comp hf
    have hnn := (ComputableInPolyTime.unary_to_binary.comp hn).comp hf
    have hz : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2)
        (encEvaluation enc) (encList encNat) := by fun_prop
    have hread : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2[i q.1]?.getD 0)
        (encEvaluation enc) encNat := by
      simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
        ComputableInPolyTime.listGetD_binary 0 hz hin
    have hguard : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => decide (i q.1 < n q.1))
        (encEvaluation enc) encBool := ComputableInPolyTime.binary_lt' hin hnn
    have hchoice := (ComputableTidilyInPolyTime.ite_decide hguard.tidy hread.tidy
      (ComputableTidilyInPolyTime.const 0)).computableInPolyTime
    exact ComputableInPolyTime.binary_mod.comp (hchoice.prod (by fun_prop))
  evaluate_eq w p z hp _ := by
    let : NeZero p := ⟨hp.ne_zero⟩
    unfold LeanCanny.CountingHierarchy.optionalCoordinate
    split_ifs <;> simp only [evaluation, MvPolynomial.eval₂_X, MvPolynomial.eval₂_zero,
      ZMod.val_natCast, ZMod.val_zero, Nat.zero_mod]

end Controlled
end LeanCanny.CountingHierarchy
