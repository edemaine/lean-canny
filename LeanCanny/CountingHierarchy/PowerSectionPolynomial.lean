/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledSubstitution
public import LeanCanny.CountingHierarchy.PointBlocks
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Power sections with the parameter block retained -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {m : ℕ}

noncomputable def powerSectionImage (e : ℕ) : Fin (m + 2) → MvPolynomial (Fin (m + 1)) ℤ :=
  Fin.cases (MvPolynomial.X 0)
    (Fin.cases (MvPolynomial.X 0 ^ e) (fun i : Fin m => MvPolynomial.X i.succ))

noncomputable def powerSectionPolynomial (e : ℕ) (P : MvPolynomial (Fin (m + 2)) ℤ) :
    MvPolynomial (Fin (m + 1)) ℤ := substitutePolynomial (powerSectionImage e) P

def powerSectionPoint (e p : ℕ) (z : List ℕ) : List ℕ :=
  z[0]?.getD 0 :: powMod p (z[0]?.getD 0) e :: z.drop 1

theorem powerSectionImage_degree (e : ℕ) (i : Fin (m + 2)) :
    (powerSectionImage e i).totalDegree ≤ e + 1 := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp [powerSectionImage]
  · exact (MvPolynomial.totalDegree_pow _ _).trans (by simp)
  · simp [powerSectionImage]

theorem powerSectionImage_mass (e : ℕ) (i : Fin (m + 2)) :
    LeanCanny.Algebra.MvMass.mass (powerSectionImage e i) ≤ 1 := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp [powerSectionImage]
  · exact (LeanCanny.Algebra.MvMass.pow_le _ _).trans_eq (by simp)
  · simp [powerSectionImage]

theorem powerSectionPoint_correct (e p : ℕ) (z : List ℕ) (i : Fin (m + 2)) (hp : p.Prime) :
    (powerSectionPoint e p z)[i.val]?.getD 0 % p = evaluation (powerSectionImage e i) p z := by
  let : NeZero p := ⟨hp.ne_zero⟩
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp only [powerSectionPoint, powerSectionImage, Fin.cases_zero, Fin.val_zero,
      List.getElem?_cons_zero, Option.getD_some, evaluation, MvPolynomial.eval₂_X, ZMod.val_natCast]
  · simp only [powerSectionPoint, powerSectionImage, Fin.cases_succ, Fin.cases_zero,
      Fin.val_succ, Fin.val_zero, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, evaluation, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
      powMod_of_ne_zero hp.ne_zero, Nat.mod_mod, ← Nat.cast_pow, ZMod.val_natCast]
  · simp only [powerSectionPoint, powerSectionImage, Fin.cases_succ, Fin.val_succ,
      List.getElem?_cons_succ, List.getElem?_drop, evaluation, MvPolynomial.eval₂_X,
      ZMod.val_natCast]
    simp only [Nat.add_comm]

@[fun_prop] theorem powerSectionPoint_polyTime {α : Type} {enc : α ↪ List Bool}
    {e p : α → ℕ} {z : α → List ℕ}
    (he : ComputableInPolyTime e enc encNat) (hp : ComputableInPolyTime p enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat)) :
    ComputableInPolyTime (fun w => powerSectionPoint (e w) (p w) (z w)) enc (encList encNat) := by
  have hv : ComputableInPolyTime (fun w => (z w)[0]?.getD 0) enc encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hz (ComputableInPolyTime.const 0)
  have hpow := computableInPolyTime_powMod hp hv he
  have hdrop := ComputableTidilyInPolyTime.listDropWithInput hz.tidy (ComputableTidilyInPolyTime.const 1)
  exact (ComputableTidilyInPolyTime.cons' hv.tidy
    (ComputableTidilyInPolyTime.cons' hpow.tidy hdrop)).computableInPolyTime

namespace Controlled

noncomputable def powerSection {α : Type} {m : α → ℕ}
    {P : (w : α) → MvPolynomial (Fin (m w + 2)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled P enc a) (hm : ComputableInPolyTime m enc encUnary)
    (e : α → ℕ) (he : ComputableInPolyTime e enc encNat) :
    Controlled (fun w => powerSectionPolynomial (e w) (P w)) enc a := by
  apply C.substitute (ComputableInPolyTime.unary_add' hm (.const 1))
    (fun w => powerSectionImage (e w)) (fun w => e w + 1)
    (ComputableInPolyTime.binary_add' he (.const 1))
    (fun w => powerSectionImage_degree (e w)) (fun w => powerSectionImage_mass (e w))
    (fun q => powerSectionPoint (e q.1) q.2.1 q.2.2)
  · have hf := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    exact powerSectionPoint_polyTime (he.comp hf) (by fun_prop) (by fun_prop)
  · exact fun w p z i hp => powerSectionPoint_correct (e w) p z i hp

end Controlled
end LeanCanny.CountingHierarchy
