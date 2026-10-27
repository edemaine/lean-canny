/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockEncoding

/-! # Native coefficients of encoded sample coordinate blocks

Free variables are encoded by monomials with polynomial-length binary
exponents. Frozen coordinates use the original rational-coordinate readers.
Only the number of free variables is unary; the block offset is binary.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockReaders
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open BoundedCriticalSampleBlockSource BoundedCriticalSampleBlockEncoding
open RationalSubstitution.IntegerBits (context selectedDegree)
open scoped Classical

def indexWord (q : List Bool) : List Bool := pairFst (selectedDegree q)
def degreeWord (q : List Bool) : List Bool := pairSnd (selectedDegree q)
theorem indexWord_FP : indexWord ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairFst_mem_FP
theorem degreeWord_FP : degreeWord ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP

theorem free_pred {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) :
    FPPred (fun q => InBlock (o (context q)) (k (context q)) (Nat.fromBitsLE (indexWord q))) := by
  have hi := BinaryFn.fromBits indexWord_FP
  have hO : BinaryFn (fun q => o (context q)) := ho.comp RationalSubstitution.IntegerBits.context_mem_FP
  have hK := BinaryFn.ofUnary (hk.comp RationalSubstitution.IntegerBits.context_mem_FP)
  exact (hO.le hi).and (hi.lt (hO.add hK))

theorem power_binary {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) :
    BinaryFn (fun q => power P read o k (context q) (Nat.fromBitsLE (indexWord q))) := by
  have hi := (BinaryFn.fromBits indexWord_FP).sub (ho.comp RationalSubstitution.IntegerBits.context_mem_FP)
  have hm : UnaryFn (fun q => min (Nat.fromBitsLE (indexWord q) - o (context q)) (k (context q))) :=
    (UnaryFn.fromBitsLE_min hi.bits_mem_FP (hk.comp RationalSubstitution.IntegerBits.context_mem_FP)).of_eq
      (fun q => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply])
  exact (BinaryFn.const 2).powUnary ((hm.add (UnaryFn.const 1)).mul
    ((width_unary h read hr).comp RationalSubstitution.IntegerBits.context_mem_FP))

def unitQuery (q : List Bool) : List Bool := pair (pair (context q) (pair (indexWord q) [])) (pairSnd q)
theorem unitQuery_FP : unitQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP (mem_FP_pair indexWord_FP (constFn_mem_FP []))) pairSnd_mem_FP

noncomputable def coefficient (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (b : Bool) (q : List Bool) : List Bool :=
  if InBlock (o (context q)) (k (context q)) (Nat.fromBitsLE (indexWord q)) then
    if b then if Nat.fromBitsLE (degreeWord q) = power P read o k (context q) (Nat.fromBitsLE (indexWord q)) then
      IndexedKroneckerReader.unitValue (unitQuery q) else []
    else IndexedKroneckerReader.unitValue q
  else BoundedCriticalSampleLineCoordinates.baseCode P b q

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (b : Bool)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P read o k b) := by
  have hi := (BinaryFn.fromBits degreeWord_FP).eq (power_binary h read hr ho hk)
  have U := SpaceFunction.ofFP _ IndexedKroneckerReader.unitValue_FP
  have E := SpaceFunction.branch _ hi.flag_mem_FP (U.precompose unitQuery unitQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have F : SpaceFunction (fun q => if b then
      (if Nat.fromBitsLE (degreeWord q) = power P read o k (context q) (Nat.fromBitsLE (indexWord q)) then
        IndexedKroneckerReader.unitValue (unitQuery q) else []) else IndexedKroneckerReader.unitValue q) := by
    cases b
    · exact U
    · exact E.congr (funext fun q => by simp only [decide_eq_true_eq, Function.comp_apply, ite_true])
  exact (SpaceFunction.branch _ (free_pred ho hk).flag_mem_FP F
    (BoundedCriticalSampleLineCoordinates.baseCode_evaluator h b ha)).congr
      (funext fun q => by simp only [coefficient, decide_eq_true_eq])

theorem packet (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (b : Bool) (u : List Bool) (i j m : ℕ) (hm : 0 < m) :
    coefficient P read o k b
      (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode (m - 1))) =
        MatrixPower.residueBits ((((encoded P read o k b u i).coeff j : ℤ)) : ZMod m) := by
  simp only [coefficient, context, indexWord, degreeWord, selectedDegree, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, encoded]
  by_cases hi : InBlock (o u) (k u) i
  · rw [ite_eq_left hi, ite_eq_left hi]
    cases b
    · exact IndexedKroneckerReader.unit_packet u i j m hm
    · simp only [ite_true]
      by_cases hj : j = power P read o k u i
      · rw [ite_eq_left hj, coeff_X_pow]
        simp only [← hj, ite_true]
        have H := IndexedKroneckerReader.unit_packet u i 0 m hm
        rw [show BinaryNatCode.encode 0 = [] from rfl] at H
        simpa only [unitQuery, context, selectedDegree, indexWord, pairFst_pair, pairSnd_pair,
          BinaryNatCode.encode, Polynomial.coeff_one_zero] using H
      · rw [ite_eq_right hj, coeff_X_pow]
        simp only [hj, ite_false, Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
        rfl
  · rw [ite_eq_right hi, ite_eq_right hi]
    exact BoundedCriticalSampleLineCoordinates.baseCode_packet P b u i j m hm

noncomputable def coordinates (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ)
    (S : RationalSubstitutionBits.Source) : RationalSubstitutionBits.Coordinates S where
  numerator := encoded P read o k true
  denominator := encoded P read o k false
  numeratorCode := coefficient P read o k true
  denominatorCode := coefficient P read o k false
  numerator_eq u i _ j m hm := packet P read o k true u i j m hm
  denominator_eq u i _ j m hm := packet P read o k false u i j m hm

end LeanCanny.Encoding.BoundedCriticalSampleBlockReaders
