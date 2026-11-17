/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedCoordinateTests
public import LeanCanny.CountingHierarchy.ControlledConditional
public import LeanCanny.CountingHierarchy.ControlledUniformSystem
public import LeanCanny.CountingHierarchy.ControlledCongruence

/-! # The selected-point equations and strict inequalities as one controlled system -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def selectionEquation {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (D : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) (i : ℕ) : MvPolynomial (Fin n) ℤ :=
  if i = 0 then F else coordinateTestPolynomial (indexedCandidatePolynomial F D hD hn word (i - 1)) hn (i - 1)

noncomputable def selectionInequality {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (D b : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) (i : ℕ) : MvPolynomial (Fin n) ℤ :=
  coordinateTestPolynomial (indexedCandidateLabel F D b hD hn word i) hn i

namespace Controlled

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}

noncomputable def selectionEquations (C : Controlled F enc a) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => selectionEquation (F q.1) (C.degreeBound q.1)
      (C.degree_le q.1) (hpos q.1) (word q.1) q.2) (encPair enc encNat) (a + 20) := by
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hsub := ComputableInPolyTime.binary_sub' hi (ComputableInPolyTime.const 1)
  have hquery : ComputableInPolyTime (fun q : α × ℕ => (q.1, q.2 - 1))
      (encPair enc encNat) (encPair enc encNat) := hw.prod hsub
  let CR := (C.indexedCandidateTests E hpos word hword).preprocess (fun q : α × ℕ => (q.1, q.2 - 1)) hquery
  let C₀ := (C.preprocess (fun q : α × ℕ => q.1) hw).mono (by omega : a ≤ a + 20)
  have hguard : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0)) (encPair enc encNat) encBool := by
    simpa only [Nat.le_zero_eq] using ComputableInPolyTime.binary_le' hi (ComputableInPolyTime.const 0)
  let CS := C₀.conditional (CR.mono (by omega : a + 11 ≤ a + 20)) (fun q => decide (q.2 = 0)) hguard
  exact CS.congr (fun q => by simp only [selectionEquation, decide_eq_true_eq])

noncomputable def selectionInequalities (C : Controlled F enc a) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => selectionInequality (F q.1) (C.degreeBound q.1) (C.massExponent q.1)
      (C.degree_le q.1) (hpos q.1) (word q.1) q.2) (encPair enc encNat) (a + 20) :=
  C.indexedLabelTests E hpos word hword

noncomputable def selectionSystem (C : Controlled F enc a) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun w => indexedEquationPositivityPolynomial
      (selectionEquation (F w) (C.degreeBound w) (C.degree_le w) (hpos w) (word w))
      (selectionInequality (F w) (C.degreeBound w) (C.massExponent w) (C.degree_le w) (hpos w) (word w))
      (n w + 1) (n w)) enc (a + 21) := by
  let CP := C.selectionEquations E hpos word hword
  let CQ := C.selectionInequalities E hpos word hword
  have hP : UniformBounds (P := fun w i => selectionEquation (F w) (C.degreeBound w)
      (C.degree_le w) (hpos w) (word w) i) CP := by
    intro w i
    exact ⟨rfl, rfl, rfl⟩
  have hQ : UniformBounds (P := fun w i => selectionInequality (F w) (C.degreeBound w) (C.massExponent w)
      (C.degree_le w) (hpos w) (word w) i) CQ := by
    intro w i
    exact ⟨rfl, rfl, rfl⟩
  have he := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.unary_to_binary.comp C.arity_computable) (ComputableInPolyTime.const 1)
  exact CP.uniformSystem CQ hP hQ E C.arity_computable (fun w => n w + 1) n he C.arity_computable

end Controlled
end LeanCanny.CountingHierarchy
