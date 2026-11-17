/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledBoundedDegreePiece
public import LeanCanny.CountingHierarchy.ControlledPreprocessing
public import LeanCanny.CountingHierarchy.ChoiceTupleNative

/-! # A short word uniformly selects a controlled closed degree-piece lift -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def wordDegreePiece {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P : (w : α) → MvPolynomial (Fin (n w + 1)) ℤ}
    (C : Controlled P enc a) (E : Decoder enc) (hn : ComputableInPolyTime n enc encUnary) :
    Controlled (fun q : α × List Bool => degreePiecePolynomial (P q.1) (C.degreeBound q.1)
      (choiceDegree (C.degreeBound q.1) q.2).val) (encPair enc encBits) (a + 2) := by
  have hw := ComputableInPolyTime.fst enc encBits
  have hword := ComputableInPolyTime.snd enc encBits
  let CW := C.preprocess (fun q : α × List Bool => q.1) hw
  exact CW.boundedDegreePiece (Decoder.pair E Decoder.bits) (hn.comp hw)
    (fun q => (choiceDegree (C.degreeBound q.1) q.2).val)
    (choiceDegree_polyTime (C.degree_computable.comp hw) hword)
    (fun q => Nat.le_of_lt_succ (choiceDegree (C.degreeBound q.1) q.2).isLt)

end LeanCanny.CountingHierarchy.Controlled
