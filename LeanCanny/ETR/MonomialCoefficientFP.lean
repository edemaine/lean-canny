/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.MonomialReaderFP
public import LeanCanny.ETR.MonomialCoefficientAtom
public import LeanCanny.ETR.TermView

/-!
# Uniform FP access to indexed source coefficient residues

The term, monomial index, and positive-modulus predecessor are FP input fields.
The shared traversal multiplies one residue per selected leaf. Every partial
accumulator fits in the positive modulus word. Thus individual source coefficients
have uniform FP residue access under the original ETR integer/term encoding.
-/

@[expose] public section

namespace LeanCanny.ETR.MonomialReader

open LeanCanny.Encoding
open LeanCanny.Algebra.MatrixPower

def coefficientRead (term index modulus : List Bool → List Bool) : List Bool → List Bool :=
  evaluate (coefficientAtom modulus) (TermView.normalize ∘ term) index (coefficientSeed modulus)

theorem coefficientRead_correct (term index modulus : List Bool → List Bool) (c : List Bool) :
    coefficientRead term index modulus c = Codec.IntegerResidue.residue
      ((TermView.term (term c)).monomialCoefficient (Nat.fromBitsLE (index c))) (Nat.fromBitsLE (modulus c) + 1) := by
  have he := evaluate_eq (R := fun c => ZMod (Nat.fromBitsLE (modulus c) + 1)) (fun _ => residueBits)
    (fun _ z => (z : ZMod _)) (fun _ _ => 1) (fun c => TermView.term (term c))
    (TermView.normalize ∘ term) index (coefficientSeed modulus) (coefficientAtom modulus)
    (fun c => TermView.normalize_eq_term (term c)) (coefficientSeed_correct modulus)
    (coefficientAtom_const modulus) (coefficientAtom_var modulus) c
  rw [coefficientRead, he]
  apply congrArg residueBits
  exact fold_coefficient_cast (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))).toMonoidHom _ _

theorem coefficientRead_mem_FP {term index modulus : List Bool → List Bool}
    (ht : term ∈ FP) (hi : index ∈ FP) (hm : modulus ∈ FP) : coefficientRead term index modulus ∈ FP := by
  have hn := mem_FP_comp ht TermView.normalize_mem_FP
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hmod
  have H := reader_mem_FP (R := fun c => ZMod (Nat.fromBitsLE (modulus c) + 1)) (fun _ => residueBits)
    (fun _ z => (z : ZMod _)) (fun _ _ => 1) (fun c => TermView.term (term c))
    (TermView.normalize ∘ term) index (coefficientSeed modulus) (coefficientAtom modulus)
    (fun c => TermView.normalize_eq_term (term c)) (coefficientSeed_correct modulus)
    (coefficientAtom_const modulus) (coefficientAtom_var modulus) hn hi
    (coefficientSeed_mem_FP hm) (coefficientAtom_mem_FP hm) p (by
      intro c k _
      let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
      rw [residueBits, BinaryNatCode.length_encode]
      apply (Nat.size_le.mpr ?_).trans (hp c)
      apply (ZMod.val_lt _).trans
      simpa only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits] using
        Nat.fromBitsLE_lt_pow_length (BinaryNat.succ (modulus c)))
  refine mem_FP_of_eq (g := coefficientRead term index modulus) H ?_
  intro c
  rw [coefficientRead_correct]
  apply congrArg residueBits
  exact fold_coefficient_cast (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))).toMonoidHom _ _

def sourceCoefficient (source : List Bool → List Bool) : List Bool → List Bool :=
  coefficientRead (source ∘ pairFst ∘ pairFst) (pairSnd ∘ pairFst) pairSnd

theorem sourceCoefficient_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : sourceCoefficient source ∈ FP := by
  have ht := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hs
  have hi := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact coefficientRead_mem_FP ht hi pairSnd_mem_FP

theorem sourceCoefficient_packet (source : List Bool → List Bool) (c : List Bool) (r m : ℕ) (hm : 0 < m) :
    sourceCoefficient source (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((TermView.term (source c)).monomialCoefficient r : ℤ) : ZMod m) := by
  rw [sourceCoefficient, coefficientRead_correct]
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  rfl

end LeanCanny.ETR.MonomialReader
