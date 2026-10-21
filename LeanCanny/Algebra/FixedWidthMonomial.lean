/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-! # FP coefficient residues of constant and variable monomials

Compare every coordinate of an arbitrary fixed-width query against a zero or
unit exponent. Short, redundant, and zero-width words retain their literal
exponent meaning. The check does not rely on canonical word encodings.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthMonomial
open LeanCanny.Encoding MvPolynomial
open RationalSubstitution.Indexed MatrixPower
open scoped Classical

variable (A W r : List Bool → ℕ) (target : List Bool → List Bool)

def expected (unit : Bool) (c : List Bool) (i : ℕ) : ℕ := if unit ∧ i = r c then 1 else 0

def Matches (unit : Bool) (c : List Bool) : Prop :=
  ∀ i < A c, FixedWidthQuery.coordinate W target c i = expected r unit c i

theorem matches_fppred (unit : Bool) (hA : UnaryFn A) (hW : UnaryFn W)
    (hr : UnaryFn r) (ht : target ∈ FP) : FPPred (Matches A W r target unit) := by
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hW.lift)) hW.lift
  have he : (fun q => BinaryNatCode.encode (expected r unit (pairFst q) (pairSnd q).length)) ∈ FP := by
    cases unit
    · exact constFn_mem_FP []
    · apply mem_FP_of_eq ((FPPred.eq UnaryFn.index hr.lift).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP []))
      intro q
      by_cases h : (pairSnd q).length = r (pairFst q) <;> simp [expected, h, BinaryNatCode.encode]
  have hm := (BinaryNat.le_fppred hs he).and (BinaryNat.le_fppred he hs)
  apply (FPPred.forall_lt hA hm).of_iff
  intro c
  simp only [Matches, pairFst_pair, pairSnd_pair, List.length_replicate, Function.comp_apply,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, FixedWidthQuery.coordinate]
  exact forall_congr' (fun i => imp_congr_right (fun _ => le_antisymm_iff.symm))

theorem matches_iff (unit : Bool) (c : List Bool) (hr : r c < A c) :
    Matches A W r target unit c ↔
      exponentVector (A c) (FixedWidthQuery.coordinate W target c) =
        if unit then Finsupp.single ⟨r c, hr⟩ 1 else 0 := by
  rw [Finsupp.ext_iff]
  simp only [exponentVector, Finsupp.coe_equivFunOnFinite_symm]
  constructor
  · intro h i
    have he := h i.val i.isLt
    cases unit <;> simpa [expected, Finsupp.single_apply, Fin.ext_iff, eq_comm] using he
  · intro h i hi
    have he := h ⟨i, hi⟩
    cases unit <;> simpa [expected, Finsupp.single_apply, Fin.ext_iff, eq_comm] using he

noncomputable def value (unit : Bool) (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (if Matches A W r target unit c then (1 : ZMod (Nat.fromBitsLE (modulus c) + 1)) else 0)

theorem value_mem_FP (unit : Bool) (modulus : List Bool → List Bool) (hA : UnaryFn A)
    (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    value A W r target unit modulus ∈ FP := by
  have hone := mem_FP_comp (mem_FP_comp hm BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  have he := (matches_fppred A W r target unit hA hW hr ht).ite_mem_FP hone (constFn_mem_FP [])
  apply mem_FP_of_eq he
  intro c
  unfold value
  by_cases h : Matches A W r target unit c
  · simp only [h, ite_true, Function.comp_apply, BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits (Nat.fromBitsLE (modulus c) + 1)
  · simp [h, residueBits, BinaryNatCode.encode]

theorem value_coefficient (unit : Bool) (modulus : List Bool → List Bool) (c : List Bool) (hr : r c < A c) :
    value A W r target unit modulus c = residueBits
      (((if unit then (MvPolynomial.X ⟨r c, hr⟩ : MvPolynomial (Fin (A c)) ℤ) else 1).coeff
        (exponentVector (A c) (FixedWidthQuery.coordinate W target c))) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold value
  rw [matches_iff A W r target unit c hr]
  cases unit <;> simp [MvPolynomial.X, MvPolynomial.coeff_monomial, MvPolynomial.coeff_one, eq_comm]

end LeanCanny.Algebra.FixedWidthMonomial
