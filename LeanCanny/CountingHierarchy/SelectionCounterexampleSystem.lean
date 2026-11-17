/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SelectionSystem
public import LeanCanny.CountingHierarchy.ControlledAppendVariables

/-! # The selected-counterexample existential system -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def selectionExtraEquation {n u : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (R : MvPolynomial (Fin (n + u)) ℤ) (D : ℕ) (hD : F.totalDegree ≤ D)
    (hn : 0 < n) (word : List Bool) (i : ℕ) : MvPolynomial (Fin (n + u)) ℤ :=
  if i = 0 then R else MvPolynomial.rename (Fin.castAdd u) (selectionEquation F D hD hn word (i - 1))

noncomputable def selectionExtraInequality {n u : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (D b : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) (i : ℕ) :
    MvPolynomial (Fin (n + u)) ℤ :=
  MvPolynomial.rename (Fin.castAdd u) (selectionInequality F D b hD hn word i)

namespace Controlled

variable {α : Type} {n u : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {F : (w : α) → MvPolynomial (Fin (n w)) ℤ} {R : (w : α) → MvPolynomial (Fin (n w + u w)) ℤ}

noncomputable def selectedCounterexampleSystem (C : Controlled F enc a)
    (CR : Controlled R enc (a + 20)) (hu : ComputableInPolyTime u enc encUnary) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun w => indexedEquationPositivityPolynomial
      (selectionExtraEquation (F w) (R w) (C.degreeBound w) (C.degree_le w) (hpos w) (word w))
      (selectionExtraInequality (u := u w) (F w) (C.degreeBound w) (C.massExponent w)
        (C.degree_le w) (hpos w) (word w)) (n w + 2) (n w)) enc (a + 21) := by
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hsub := ComputableInPolyTime.binary_sub' hi (ComputableInPolyTime.const 1)
  have hquery : ComputableInPolyTime (fun q : α × ℕ => (q.1, q.2 - 1))
      (encPair enc encNat) (encPair enc encNat) := hw.prod hsub
  let CPpad := (C.selectionEquations E hpos word hword).appendVariables (fun q => u q.1) (hu.comp hw)
  let CPshift := CPpad.preprocess (fun q : α × ℕ => (q.1, q.2 - 1)) hquery
  let CQ := (C.selectionInequalities E hpos word hword).appendVariables (fun q => u q.1) (hu.comp hw)
  let C₀ := CR.preprocess (fun q : α × ℕ => q.1) hw
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0)) (encPair enc encNat) encBool := by
    simpa only [Nat.le_zero_eq] using ComputableInPolyTime.binary_le' hi (ComputableInPolyTime.const 0)
  let CC := C₀.conditional CPshift (fun q => decide (q.2 = 0)) hguard
  let CP := CC.congr (Q := fun q : α × ℕ => selectionExtraEquation (F q.1) (R q.1)
    (C.degreeBound q.1) (C.degree_le q.1) (hpos q.1) (word q.1) q.2)
    (fun q => by simp only [selectionExtraEquation, decide_eq_true_eq])
  have hP : UniformBounds (P := fun w i => selectionExtraEquation (F w) (R w) (C.degreeBound w)
      (C.degree_le w) (hpos w) (word w) i) CP := by
    intro w i
    exact ⟨rfl, rfl, rfl⟩
  have hQ : UniformBounds (P := fun w i => selectionExtraInequality (u := u w) (F w) (C.degreeBound w)
      (C.massExponent w) (C.degree_le w) (hpos w) (word w) i) CQ := by
    intro w i
    exact ⟨rfl, rfl, rfl⟩
  have he := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.unary_to_binary.comp C.arity_computable) (ComputableInPolyTime.const 2)
  exact CP.uniformSystem CQ hP hQ E (ComputableInPolyTime.unary_add' C.arity_computable hu)
    (fun w => n w + 2) n he C.arity_computable

end Controlled
end LeanCanny.CountingHierarchy
