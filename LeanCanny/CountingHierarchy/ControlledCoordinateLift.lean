/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledRenaming
public import LeanCanny.CountingHierarchy.ControlledUnivariate

/-! # Lifting controlled univariate tests to a selected coordinate -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def onCoordinate {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : α → Polynomial ℤ} (C : Controlled (fun w => liftUnivariate (P w)) enc a)
    (hn : ComputableInPolyTime n enc encUnary) (i : (w : α) → Fin (n w))
    (hi : ComputableInPolyTime (fun w => (i w).val) enc encNat) :
    Controlled (fun w => MvPolynomial.rename (fun _ : Fin 1 => i w) (liftUnivariate (P w))) enc a := by
  apply C.rename hn (fun w _ => i w) (fun q => [q.2[(i q.1).val]?.getD 0])
  · have hf := ComputableInPolyTime.fst enc (encList encNat)
    have hz := ComputableInPolyTime.snd enc (encList encNat)
    have hread : ComputableInPolyTime (fun q : α × List ℕ => q.2[(i q.1).val]?.getD 0)
        (encPair enc (encList encNat)) encNat := by
      simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
        ComputableInPolyTime.listGetD_binary 0 hz (hi.comp hf)
    exact (ComputableTidilyInPolyTime.cons' hread.tidy (ComputableTidilyInPolyTime.const [])).computableInPolyTime
  · intro w z j
    have h : j = 0 := Fin.eq_zero j
    subst j
    simp only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]

end LeanCanny.CountingHierarchy.Controlled
