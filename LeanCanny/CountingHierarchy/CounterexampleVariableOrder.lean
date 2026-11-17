/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledRenaming
public import LeanCanny.CountingHierarchy.PointBlocks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # The counterexample polynomial in parameter-inverse and witness coordinates -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {n m : ℕ}

def counterexampleVariable : Fin (n + m) → Fin ((m + 1) + n) :=
  Fin.addCases (Fin.natAdd (m + 1)) (fun i : Fin m => Fin.castAdd n i.succ)

noncomputable def counterexamplePolynomial (P : MvPolynomial (Fin (n + m)) ℤ) :
    MvPolynomial (Fin ((m + 1) + n)) ℤ := MvPolynomial.rename counterexampleVariable P

theorem eval_counterexamplePolynomial {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (P : MvPolynomial (Fin (n + m)) ℤ) (c : Fin (m + 1) → S) (z : Fin n → S) :
    MvPolynomial.eval₂ phi (Fin.addCases c z) (counterexamplePolynomial P) =
      MvPolynomial.eval₂ phi (Fin.addCases z (fun i => c i.succ)) P := by
  rw [counterexamplePolynomial, MvPolynomial.eval₂_rename]
  congr 2
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Function.comp_def, counterexampleVariable, Fin.addCases_left, Fin.addCases_right]

namespace Controlled

noncomputable def counterexampleOrder {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}
    (C : Controlled P enc a) (hn : ComputableInPolyTime n enc encUnary)
    (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => counterexamplePolynomial (P w)) enc a := by
  apply C.rename (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_add' hm (.const 1)) hn)
    (fun _ => counterexampleVariable)
    (fun q => joinedPoint (n q.1) (m q.1) (q.2.drop (m q.1 + 1)) (q.2.drop 1))
  · have hw := ComputableInPolyTime.fst enc (encList encNat)
    have hz := ComputableInPolyTime.snd enc (encList encNat)
    have hm' := hm.comp hw
    have hdrop := (ComputableTidilyInPolyTime.listDropWithInput hz.tidy
      (ComputableInPolyTime.unary_add' hm' (.const 1)).tidy).computableInPolyTime
    have hparams := (ComputableTidilyInPolyTime.listDropWithInput hz.tidy (ComputableTidilyInPolyTime.const 1)).computableInPolyTime
    exact joinedPoint_polyTime (hn.comp hw) hm' hdrop hparams
  · intro w p i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.val_castAdd, joinedPoint_left]
      simp only [List.getElem?_drop, counterexampleVariable, Fin.addCases_left, Fin.val_natAdd]
    · rw [Fin.val_natAdd, joinedPoint_right]
      simp only [List.getElem?_drop, counterexampleVariable, Fin.addCases_right,
        Fin.val_castAdd, Fin.val_succ, Nat.add_comm]

end Controlled
end LeanCanny.CountingHierarchy
