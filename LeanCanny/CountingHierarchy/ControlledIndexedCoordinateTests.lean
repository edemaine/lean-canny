/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedLabels
public import LeanCanny.CountingHierarchy.ControlledCoordinateLift

/-! # Candidate equations and label inequalities in the original coordinate space -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def coordinateTestPolynomial {n : ℕ} (p : Polynomial ℤ) (hn : 0 < n) (i : ℕ) :
    MvPolynomial (Fin n) ℤ :=
  MvPolynomial.rename (fun _ : Fin 1 => (⟨i % n, Nat.mod_lt _ hn⟩ : Fin n)) (liftUnivariate p)

theorem eval_coordinateTestPolynomial {n : ℕ} {S : Type*} [CommRing S] (phi : ℤ →+* S)
    (p : Polynomial ℤ) (hn : 0 < n) (i : ℕ) (x : Fin n → S) :
    MvPolynomial.eval₂ phi x (coordinateTestPolynomial p hn i) =
      p.eval₂ phi (x ⟨i % n, Nat.mod_lt _ hn⟩) := by
  rw [coordinateTestPolynomial, MvPolynomial.eval₂_rename, eval_liftUnivariate]
  rfl

namespace Controlled

variable {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}

noncomputable def indexedCandidateTests (C : Controlled F enc a) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => coordinateTestPolynomial
      (indexedCandidatePolynomial (F q.1) (C.degreeBound q.1) (C.degree_le q.1) (hpos q.1) (word q.1) q.2)
      (hpos q.1) q.2) (encPair enc encNat) (a + 11) := by
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  exact (C.indexedCandidates E hpos word hword).onCoordinate (C.arity_computable.comp hw)
    (fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hpos q.1)⟩)
    (ComputableInPolyTime.binary_mod.comp
      (hi.prod ((ComputableInPolyTime.unary_to_binary.comp C.arity_computable).comp hw)))

noncomputable def indexedLabelTests (C : Controlled F enc a) (E : Decoder enc)
    (hpos : ∀ w, 0 < n w) (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => coordinateTestPolynomial
      (indexedCandidateLabel (F q.1) (C.degreeBound q.1) (C.massExponent q.1)
        (C.degree_le q.1) (hpos q.1) (word q.1) q.2) (hpos q.1) q.2)
      (encPair enc encNat) (a + 20) := by
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  exact (C.indexedLabels E hpos word hword).onCoordinate (C.arity_computable.comp hw)
    (fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hpos q.1)⟩)
    (ComputableInPolyTime.binary_mod.comp
      (hi.prod ((ComputableInPolyTime.unary_to_binary.comp C.arity_computable).comp hw)))

end Controlled
end LeanCanny.CountingHierarchy
