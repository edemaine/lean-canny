/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledBoundedCandidate
public import LeanCanny.CountingHierarchy.ControlledPreprocessing
public import LeanCanny.CountingHierarchy.ChoiceTupleNative

/-! # One controlled family for all word-selected coordinate candidates -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def indexedCandidatePolynomial {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (D : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) (i : ℕ) : Polynomial ℤ :=
  addressedCandidateCoordinate F D hD ⟨i % n, Nat.mod_lt _ hn⟩
    (choiceIndex (candidateIndexBound n D) word i)

namespace Controlled

noncomputable def indexedCandidates {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) (hpos : ∀ w, 0 < n w)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => liftUnivariate
      (indexedCandidatePolynomial (F q.1) (C.degreeBound q.1) (C.degree_le q.1) (hpos q.1) (word q.1) q.2))
        (encPair enc encNat) (a + 11) := by
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  let CW := C.preprocess (fun q : α × ℕ => q.1) hw
  let idx : (q : α × ℕ) → Fin (n q.1) := fun q => ⟨q.2 % n q.1, Nat.mod_lt _ (hpos q.1)⟩
  have hidx : ComputableInPolyTime (fun q : α × ℕ => (idx q).val) (encPair enc encNat) encNat := by
    exact ComputableInPolyTime.binary_mod.comp
      (hi.prod ((ComputableInPolyTime.unary_to_binary.comp C.arity_computable).comp hw))
  have hH := candidateIndexBound_polyTime C.arity_computable C.degree_computable
  have hj := choiceIndex_polyTime (hH.comp hw) hi (hword.comp hw)
  exact CW.boundedCandidate (Decoder.pair E Decoder.nat) idx hidx
    (fun q => choiceIndex (candidateIndexBound (n q.1) (C.degreeBound q.1)) (word q.1) q.2) hj
    (fun q => choiceIndex_le _ _ _)

end Controlled
end LeanCanny.CountingHierarchy
