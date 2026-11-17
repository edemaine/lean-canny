/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledIndexedCandidates
public import LeanCanny.CountingHierarchy.ControlledPrescribedLabel

/-! # Word-selected prescribed-root labels for all candidate coordinates -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def indexedCandidateLabel {n : ℕ} (F : MvPolynomial (Fin n) ℤ)
    (D b : ℕ) (hD : F.totalDegree ≤ D) (hn : 0 < n) (word : List Bool) (i : ℕ) : Polynomial ℤ :=
  let L := choiceLabel (candidateDegree n D) word i
  fingerprintIntegerRootLabel (indexedCandidatePolynomial F D hD hn word i) 1
    (candidateDegree n D) (candidateMassExponent n D b) L.modulus L.parameter L.target

namespace Controlled

noncomputable def indexedLabels {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {F : (w : α) → MvPolynomial (Fin (n w)) ℤ}
    (C : Controlled F enc a) (E : Decoder enc) (hpos : ∀ w, 0 < n w)
    (word : α → List Bool) (hword : ComputableInPolyTime word enc encBits) :
    Controlled (fun q : α × ℕ => liftUnivariate
      (indexedCandidateLabel (F q.1) (C.degreeBound q.1) (C.massExponent q.1)
        (C.degree_le q.1) (hpos q.1) (word q.1) q.2)) (encPair enc encNat) (a + 20) := by
  let CC := C.indexedCandidates E hpos word hword
  have hw := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hwords := hword.comp hw
  let L := fun q : α × ℕ => choiceLabel (CC.degreeBound q) (word q.1) q.2
  have hL (q : α × ℕ) : (L q).Bounded (CC.degreeBound q) := choiceLabel_bounded _ _ _
  let CL := CC.prescribedLabel (Decoder.pair E Decoder.nat) L hL
    (choiceLabel_modulus_polyTime CC.degree_computable hi hwords)
    (choiceLabel_parameter_polyTime CC.degree_computable hi hwords)
    (choiceLabel_target_polyTime CC.degree_computable hi hwords)
  exact CL.mono (by omega : max (a + 11 + 1) 3 + 8 ≤ a + 20)

end Controlled
end LeanCanny.CountingHierarchy
