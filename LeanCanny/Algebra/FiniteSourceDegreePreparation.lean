/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedAnnihilatorReaders
public import LeanCanny.Algebra.ValidatedPolynomialReaders
public import LeanCanny.Algebra.IntegerPolynomialDegreeSpace
public import LeanCanny.Encoding.FixedWidthNatVectorSpace
public import LeanCanny.Encoding.FixedWidthWrite

/-! # Preparing exact degrees for a finite source in native polynomial space

Only degree and mass upper bounds are FP. A polynomial-size degree table is
computed with the original space coefficient reader, then checked contexts
supply total exact FP degree metadata. Outside the finite source, X is used.
Prepared contexts recover every original finite polynomial literally.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteSourceDegreePreparation
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical

attribute [local irreducible] BinaryNat.normalize

noncomputable def padded (F : Family) (count : List Bool → ℕ) (p : List Bool) : ℤ[X] :=
  (PaddedAnnihilatorBits.family F count).polynomial p

theorem padded_packet (F : Family) (count : List Bool → ℕ) (c : List Bool) (i : ℕ)
    (hi : i < count c) : padded F count (pair c (BinaryNatCode.encode i)) =
      F.polynomial (pair c (BinaryNatCode.encode i)) := by
  rw [padded, PaddedAnnihilatorBits.polynomial_packet, ite_eq_left hi]

def originalQuery (q : List Bool) : List Bool :=
  pair (pair (PaddedAnnihilatorBits.input (context q)) (selectedDegree q)) (pairSnd q)

theorem originalQuery_FP : originalQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP PaddedAnnihilatorBits.input_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem paddedEvaluator (F : Family) (count : List Bool → ℕ) (hn : UnaryFn count)
    (E : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) :
    SpaceFunction (PrimitivePairBits.coefficient (padded F count)) := by
  have hp := (PaddedAnnihilatorBits.valid_FP hn).comp RationalSubstitution.IntegerBits.context_mem_FP
  have Ep := SpaceFunction.ofFP
    (PaddedAnnihilatorBits.paddingCoefficient ∘ PrimitivePairBits.modularCoefficientQuery)
    (mem_FP_comp PrimitivePairBits.modularCoefficientQuery_FP PaddedAnnihilatorBits.paddingCoefficient_FP)
  have R := SpaceFunction.branch (fun q => decide (PaddedAnnihilatorBits.valid count (context q)))
    hp.flag_mem_FP (E.precompose originalQuery originalQuery_FP) Ep
  refine R.congr (funext fun q => ?_)
  by_cases hv : PaddedAnnihilatorBits.valid count (context q)
  · have hv' : PaddedAnnihilatorBits.valid count (pairFst (pairFst q)) := hv
    simp only [Function.comp_apply, PrimitivePairBits.coefficient,
      originalQuery, padded, PaddedAnnihilatorBits.family, context, selectedDegree, mValue,
      pairFst_pair, pairSnd_pair]
    simp only [hv', decide_true, ite_true]
  · have hpad' : PaddedAnnihilatorBits.paddingCoefficient (PrimitivePairBits.modularCoefficientQuery q) =
        PrimitivePairBits.coefficient (fun _ => (X : ℤ[X])) q := by
      have he : BinaryNat.normalize (selectedDegree q) = [true] ↔
          Nat.fromBitsLE (selectedDegree q) = 1 := by
        rw [BinaryNat.normalize_eq_bits]
        change BinaryNatCode.encode (Nat.fromBitsLE (selectedDegree q)) = BinaryNatCode.encode 1 ↔ _
        exact BinaryNatCode.encode_injective.eq_iff
      simp only [PaddedAnnihilatorBits.paddingCoefficient, PrimitivePairBits.modularCoefficientQuery,
        pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient, selectedDegree]
      change (if BinaryNat.normalize (selectedDegree q) = [true] then
        MatrixPower.ArithmeticBits.one (BinaryNat.succ (pairSnd q)) else []) =
          RationalSubstitution.IntegerBits.coefficientResidue
            ((X : ℤ[X]).coeff (Nat.fromBitsLE (selectedDegree q))) (mValue q)
      simp only [he, coeff_X]
      by_cases hk : Nat.fromBitsLE (selectedDegree q) = 1
      · simp only [hk, ite_true]
        simpa only [BinaryNat.succ_eq_bits, BinaryNatCode.encode,
          RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_one, mValue] using
          MatrixPower.ArithmeticBits.one_residueBits (mValue q)
      · simp only [hk, Ne.symm hk, ite_false,
          RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_zero,
          MatrixPower.residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]
    have hv' : ¬ PaddedAnnihilatorBits.valid count (pairFst (pairFst q)) := hv
    simp only [Function.comp_apply, hpad',
      PrimitivePairBits.coefficient, padded, PaddedAnnihilatorBits.family, context]
    simp only [hv', decide_false, Bool.false_eq_true, ite_false]

variable (F : Family) (count D b : List Bool → ℕ)
variable (hdegree : ∀ c i, i < count c →
  (F.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hmass : ∀ c i, i < count c →
  coefficientMass (F.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2 ^ b c)

include hdegree in
theorem padded_degree (p : List Bool) : (padded F count p).natDegree ≤ D (pairFst p) + 1 := by
  change (if PaddedAnnihilatorBits.valid count p then
    F.polynomial (PaddedAnnihilatorBits.input p) else X).natDegree ≤ _
  split_ifs with hp
  · simpa only [PaddedAnnihilatorBits.input, BinaryNat.normalize_eq_bits, BinaryNatCode.encode] using
      (hdegree (pairFst p) (Nat.fromBitsLE (pairSnd p)) hp).trans (Nat.le_succ _)
  · simp only [natDegree_X]
    omega

include hmass in
theorem padded_mass (p : List Bool) : coefficientMass (padded F count p) ≤ 2 ^ b (pairFst p) := by
  change coefficientMass (if PaddedAnnihilatorBits.valid count p then
    F.polynomial (PaddedAnnihilatorBits.input p) else X) ≤ _
  split_ifs with hp
  · simpa only [PaddedAnnihilatorBits.input, BinaryNat.normalize_eq_bits, BinaryNatCode.encode] using
      hmass (pairFst p) (Nat.fromBitsLE (pairSnd p)) hp
  · have hmx : coefficientMass (X : ℤ[X]) = 1 := by
      simpa only [pow_one] using coefficientMass_X_pow 1
    simpa only [hmx] using Nat.one_le_two_pow (n := b (pairFst p))

include hmass in
noncomputable def paddedFamily : Family where
  polynomial := padded F count
  height p := b (pairFst p)
  coefficient_bound p k := (coeff_natAbs_le_coefficientMass _ k).trans (padded_mass F count b hmass p)

include hdegree hmass in
theorem degreeEvaluator (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) :
    SpaceFunction (fun p => BinaryNatCode.encode (padded F count p).natDegree) :=
  IntegerPolynomialBits.degreeEvaluator (padded F count) (paddedEvaluator F count hn E)
    (fun p => D (pairFst p) + 1) (fun p => b (pairFst p))
    ((hD.add (BinaryFn.const 1)).comp pairFst_mem_FP) (hb.comp pairFst_mem_FP)
    (padded_degree F count D hdegree) (padded_mass F count b hmass)

def width (D : List Bool → ℕ) (c : List Bool) : ℕ := (D c + 1).size

theorem width_unary {D : List Bool → ℕ} (hD : BinaryFn D) : UnaryFn (width D) := by
  have h := UnaryFn.length ((hD.add (BinaryFn.const 1)).bits_mem_FP)
  exact h.of_eq (fun c => Nat.size_eq_bits_len (D c + 1))

noncomputable def prepare (c : List Bool) : List Bool :=
  pair c (FixedWidthNatVector.encode (count c) (width D c)
    (fun i => (padded F count (pair c (BinaryNatCode.encode i))).natDegree))

include hdegree hmass in
theorem prepareEvaluator (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) : SpaceFunction (prepare F count D) := by
  have R := FixedWidthNatVector.encodeEvaluator count (width D)
    (fun c i => (padded F count (pair c (BinaryNatCode.encode i))).natDegree)
    hn (width_unary hD) (fun p => BinaryNatCode.encode (padded F count p).natDegree)
    (degreeEvaluator F count D b hdegree hmass hn hD hb E) (fun _ _ => rfl)
  exact R.withInput

def checkedInput (p : List Bool) : List Bool :=
  pair (PaddedAnnihilatorBits.input (pair (pairFst (pairFst p)) (pairSnd p)))
    (FixedWidthQuery.read (count ∘ pairFst) (width D ∘ pairFst) pairSnd p)

theorem checkedInput_FP (hn : UnaryFn count) (hD : BinaryFn D) : checkedInput count D ∈ FP := by
  have hi := mem_FP_comp
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) PaddedAnnihilatorBits.input_FP
  have hr := FixedWidthQuery.read_mem_FP (hn.comp pairFst_mem_FP)
    ((width_unary hD).comp pairFst_mem_FP) pairSnd_mem_FP
  exact mem_FP_pair hi hr

include hmass in
noncomputable def family : Family :=
  (ValidatedDegreeBits.family (paddedFamily F count b hmass)).reindex (checkedInput count D)

include hmass in
theorem family_height (p : List Bool) :
    (family F count D b hmass).height p = b (pairFst (pairFst p)) := by
  simp only [family, SeparableBits.Family.reindex, ValidatedDegreeBits.family, paddedFamily,
    checkedInput, PaddedAnnihilatorBits.input, pairFst_pair]

include hmass in
theorem family_nonzero
    (hne : ∀ c i, i < count c → F.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (p : List Bool) : (family F count D b hmass).polynomial p ≠ 0 := by
  change (ValidatedDegreeBits.family (paddedFamily F count b hmass)).polynomial
    (checkedInput count D p) ≠ 0
  apply ValidatedDegreeBits.family_ne_zero
  intro c
  exact PaddedAnnihilatorBits.nonzero F count hne c

def degreeBudget (D : List Bool → ℕ) (c : List Bool) : ℕ := 2 ^ width D c

theorem degreeBudget_binary {D : List Bool → ℕ} (hD : BinaryFn D) : BinaryFn (degreeBudget D) :=
  (BinaryFn.const 2).powUnary (width_unary hD)

include hmass in
theorem family_degree (c : List Bool) (i : ℕ) :
    ((family F count D b hmass).polynomial (pair c (BinaryNatCode.encode i))).natDegree <
      degreeBudget D (pairFst c) := by
  change (ValidatedDegreeBits.checked (padded F count)
    (checkedInput count D (pair c (BinaryNatCode.encode i)))).natDegree < _
  rw [ValidatedDegreeBits.checked_degree]
  simp only [checkedInput, pairSnd_pair]
  rw [FixedWidthQuery.read_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact FixedWidthQuery.entry_lt (count ∘ pairFst) (width D ∘ pairFst) pairSnd c i

@[simp] theorem prepare_source (c : List Bool) : pairFst (prepare F count D c) = c := by
  simp only [prepare, pairFst_pair]

@[simp] theorem prepare_table_length (c : List Bool) :
    (pairSnd (prepare F count D c)).length = count c * width D c := by
  simp only [prepare, pairSnd_pair, FixedWidthNatVector.length_encode]

include hdegree hmass in
noncomputable def readers (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b)
    (E : SpaceFunction (PrimitivePairBits.coefficient F.polynomial)) : Readers (family F count D b hmass) := by
  have Ep := (paddedEvaluator F count hn E).precompose
    PrimitivePairBits.modularCoefficientQuery PrimitivePairBits.modularCoefficientQuery_FP
  have Ep' : SpaceFunction (ValidatedDegreeBits.coefficient (padded F count)) :=
    Ep.congr (funext fun q => by
      simp only [Function.comp_apply, PrimitivePairBits.coefficient, PrimitivePairBits.modularCoefficientQuery,
        context, selectedDegree, mValue, pairFst_pair, pairSnd_pair,
        ValidatedDegreeBits.coefficient, ValidatedDegreeBits.context, ValidatedDegreeBits.modulus]
      rfl)
  exact (ValidatedDegreeBits.readers (paddedFamily F count b hmass) (hb.comp pairFst_mem_FP) Ep'
    (degreeEvaluator F count D b hdegree hmass hn hD hb E)).reindex
      (checkedInput count D) (checkedInput_FP count D hn hD)

include hdegree hmass in
theorem prepared_polynomial (c : List Bool) (i : ℕ) (hi : i < count c) :
    (family F count D b hmass).polynomial (pair (prepare F count D c) (BinaryNatCode.encode i)) =
      F.polynomial (pair c (BinaryNatCode.encode i)) := by
  have hfit : (padded F count (pair c (BinaryNatCode.encode i))).natDegree < 2 ^ width D c := by
    rw [padded_packet F count c i hi]
    exact (hdegree c i hi).trans_lt ((Nat.lt_succ_self _).trans (Nat.lt_size_self (D c + 1)))
  have hr : checkedInput count D (pair (prepare F count D c) (BinaryNatCode.encode i)) =
      pair (pair c (BinaryNatCode.encode i))
        (BinaryNatCode.encode (padded F count (pair c (BinaryNatCode.encode i))).natDegree) := by
    simp only [checkedInput, prepare, pairFst_pair, pairSnd_pair,
      PaddedAnnihilatorBits.input_packet]
    rw [FixedWidthQuery.read_packet]
    simp only [FixedWidthQuery.entry, Function.comp_apply, pairFst_pair, hi, ite_true,
      FixedWidthQuery.coordinate, pairSnd_pair]
    rw [FixedWidthNatVector.decode_block _ _ _ i hi hfit]
  change (ValidatedDegreeBits.family (paddedFamily F count b hmass)).polynomial
    (checkedInput count D (pair (prepare F count D c) (BinaryNatCode.encode i))) = _
  rw [hr]
  change ValidatedDegreeBits.checked (padded F count)
    (pair (pair c (BinaryNatCode.encode i))
      (BinaryNatCode.encode (padded F count (pair c (BinaryNatCode.encode i))).natDegree)) = _
  rw [ValidatedDegreeBits.checked_packet]
  exact padded_packet F count c i hi

end LeanCanny.Algebra.FiniteSourceDegreePreparation
