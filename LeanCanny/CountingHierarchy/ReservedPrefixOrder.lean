/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledRenaming
public import LeanCanny.CountingHierarchy.PointBlocks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Reserving an original variable prefix as the outer real-quantifier block -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {M r : ℕ}

def reservedPrefixVariable (hr : r ≤ M) (i : Fin M) : Fin ((M - r) + r) :=
  if h : i.val < r then Fin.natAdd (M - r) ⟨i.val, h⟩
  else Fin.castAdd r ⟨i.val - r, by have := i.isLt; omega⟩

noncomputable def reservedPrefixPolynomial (P : MvPolynomial (Fin M) ℤ) (hr : r ≤ M) :
    MvPolynomial (Fin ((M - r) + r)) ℤ := MvPolynomial.rename (reservedPrefixVariable hr) P

theorem eval_reservedPrefixPolynomial {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (P : MvPolynomial (Fin M) ℤ) (hr : r ≤ M) (z : Fin (M - r) → S) (x : Fin r → S) :
    MvPolynomial.eval₂ phi (Fin.addCases z x) (reservedPrefixPolynomial P hr) =
      MvPolynomial.eval₂ phi (fun i : Fin M => if h : i.val < r then x ⟨i.val, h⟩
        else z ⟨i.val - r, by have := i.isLt; omega⟩) P := by
  rw [reservedPrefixPolynomial, MvPolynomial.eval₂_rename]
  congr 2
  funext i
  simp only [Function.comp_def, reservedPrefixVariable]
  split_ifs
  · rw [Fin.addCases_right]
  · rw [Fin.addCases_left]

namespace Controlled

noncomputable def reservedPrefix {α : Type} {M r : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (M w)) ℤ}
    (C : Controlled P enc a) (hr : ComputableInPolyTime r enc encUnary) (hbound : ∀ w, r w ≤ M w) :
    Controlled (fun w => reservedPrefixPolynomial (P w) (hbound w)) enc a := by
  have hn := ComputableInPolyTime.unary_sub' C.arity_computable hr
  apply C.rename (ComputableInPolyTime.unary_add' hn hr) (fun w => reservedPrefixVariable (hbound w))
    (fun q => joinedPoint (r q.1) (M q.1 - r q.1) (q.2.drop (M q.1 - r q.1)) q.2)
  · have hw := ComputableInPolyTime.fst enc (encList encNat)
    have hz := ComputableInPolyTime.snd enc (encList encNat)
    have hn' := hn.comp hw
    have hdrop := (ComputableTidilyInPolyTime.listDropWithInput hz.tidy hn'.tidy).computableInPolyTime
    exact joinedPoint_polyTime (hr.comp hw) hn' hdrop hz
  · intro w z i
    by_cases hi : i.val < r w
    · have hget := joinedPoint_left (r w) (M w - r w) (z.drop (M w - r w)) z ⟨i.val, hi⟩
      simpa only [reservedPrefixVariable, dite_eq_left hi, Fin.val_natAdd, List.getElem?_drop] using hget
    · have hj : i.val - r w < M w - r w := by have := i.isLt; omega
      have hget := joinedPoint_right (r w) (M w - r w) (z.drop (M w - r w)) z ⟨i.val - r w, hj⟩
      have hge : r w ≤ i.val := by omega
      rw [Nat.add_sub_of_le hge] at hget
      simpa only [reservedPrefixVariable, dite_eq_right hi, Fin.val_castAdd] using hget

end Controlled
end LeanCanny.CountingHierarchy
