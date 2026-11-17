/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledLiftedCoefficient
public import LeanCanny.CountingHierarchy.ControlledBoundedSum
public import LeanCanny.CountingHierarchy.ControlledPreprocessing
public import LeanCanny.CountingHierarchy.ControlledSelection
public import LeanCanny.CountingHierarchy.ControlledCongruence

/-! # Controlled closed degree-piece lifts -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators Classical

noncomputable def degreePiece {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc) (hn : ComputableInPolyTime n enc encUnary)
    (N d : α → ℕ) (hN : ComputableInPolyTime N enc encNat) (hd : ComputableInPolyTime d enc encNat) :
    Controlled (fun w => degreePiecePolynomial (P w) (N w) (d w)) enc (a + 2) := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hj := ComputableInPolyTime.snd enc encNat
  let CK := (C.preprocess (fun q : α × ℕ => q.1) hf).liftedCoefficient
    (Decoder.pair E Decoder.nat) (hn.comp hf) (fun q => q.2) hj
  let CS := CK.pow (fun _ => 2) (ComputableInPolyTime.const 2)
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (d q.1 < q.2)) (encPair enc encNat) encBool := by
    have := hd.comp hf
    fun_prop
  let CT := CS.select (fun q => decide (d q.1 < q.2)) hguard
  have hsum := boundedSum (P := fun w j =>
    if decide (d w < j) then liftedFirstCoefficient (P w) j ^ 2 else 0) CT E (ComputableInPolyTime.unary_add' hn (.const 1))
    (fun w => N w + 1) (fun w => C.degreeBound w * 2) (fun w => C.massExponent w * 2)
    (fun w => max (C.cutoff w) (max (C.degreeBound w) (N w)) + 1)
    (ComputableInPolyTime.binary_add' hN (.const 1))
    (ComputableInPolyTime.binary_mul' C.degree_computable (.const 2))
    (ComputableInPolyTime.binary_mul' C.mass_computable (.const 2))
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_max' C.cutoff_computable
      (ComputableInPolyTime.binary_max' C.degree_computable hN)) (.const 1))
    (fun w i _ => by
      have h := CT.degree_le (w, i)
      exact h)
    (fun w i _ => by
      have h := CT.mass_le (w, i)
      exact h)
    (fun w i hi => by
      change max (C.cutoff w) (max (C.degreeBound w) i) + 1 ≤ _
      have hiN : i ≤ N w := by omega
      exact Nat.add_le_add_right (max_le_max le_rfl (max_le_max le_rfl hiN)) 1)
  let Cd := C.liftedCoefficient E hn d hd
  let X₀ := coordinate (a := a + 1) (ComputableInPolyTime.unary_add' hn (.const 1))
    (fun _ => (0 : Fin (n _ + 1))) (ComputableInPolyTime.const 0)
  let one := constant (a := a + 1) (ComputableInPolyTime.unary_add' hn (.const 1))
    (fun _ => (1 : ℤ)) (ComputableInPolyTime.const 1)
  let base := ((Cd.mul X₀).sub one).pow (fun _ => 2) (ComputableInPolyTime.const 2)
  have h := (base.mono (by omega : a + 1 ≤ a + 2)).add hsum
  exact h.congr (fun w => by
    simp only [degreePiecePolynomial, decide_eq_true_eq, MvPolynomial.C_1])

end LeanCanny.CountingHierarchy.Controlled
