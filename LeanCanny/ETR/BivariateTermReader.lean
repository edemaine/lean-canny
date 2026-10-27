/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.BivariateTermSubstitution
public import LeanCanny.ETR.EncodedRationalSubstitution
public import LeanCanny.Algebra.IndexedKroneckerReader

/-! # Native bivariate coefficients after substitution in original terms

The radix bounds both the original coordinates and the substituted term.
Queries beyond the inner degree range return zero, preventing aliases between
the two variables. No expanded term or coefficient array is stored.
-/

@[expose] public section
namespace LeanCanny.ETR.BivariateTermReader
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open RationalSubstitutionBits
open scoped Classical

noncomputable def polynomial (S : Source) (F : BivariateQueryProductBits.Family) (c : List Bool) : (ℤ[X])[X] :=
  (S.syntax c).eval (F.polynomial c)

def radix (S : Source) (F : BivariateQueryProductBits.Family) (c : List Bool) : ℕ :=
  ((S.normalized c).length + 1) * F.parameterDegree c + 1

theorem size_eq (S : Source) (c : List Bool) : (S.normalized c).length = (S.syntax c).toData.size := by
  rw [S.normalized_eq, Data.length_toBits]

theorem radix_binary (S : Source) (hS : S.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : BinaryFn (radix S F) :=
  (((BinaryFn.ofUnary (UnaryFn.length (S.normalized_mem_FP hS))).add (BinaryFn.const 1)).mul
    A.parameterDegree_binary).add (BinaryFn.const 1)

theorem coordinate_inner_lt (S : Source) (F : BivariateQueryProductBits.Family) (c : List Bool) :
    F.parameterDegree c < radix S F c := by
  unfold radix
  nlinarith

theorem inner_lt (S : Source) (F : BivariateQueryProductBits.Family) (c : List Bool) (j : ℕ) :
    ((polynomial S F c).coeff j).natDegree < radix S F c := by
  have h := (S.syntax c).eval_innerDegree_le_size (F.polynomial c) (F.parameterDegree c)
    (F.coefficient_degree c) j
  unfold polynomial radix
  rw [size_eq]
  nlinarith

noncomputable def coordinates (S : Source) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : Coordinates S where
  numerator c i := PolynomialKronecker.encode (radix S F c) (F.polynomial c i)
  denominator _ _ := 1
  numeratorCode := IndexedKroneckerReader.value A (radix S F)
  denominatorCode := IndexedKroneckerReader.unitValue
  numerator_eq c i _ k m hm := IndexedKroneckerReader.packet A _ (coordinate_inner_lt S F) c i k m hm
  denominator_eq c i _ k m hm := IndexedKroneckerReader.unit_packet c i k m hm

theorem coordinates_polynomial (S : Source) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) (c : List Bool) :
    (coordinates S A).family.polynomial c = PolynomialKronecker.encode (radix S F c) (polynomial S F c) := by
  rw [polynomial, Term.eval_hom]
  rw [(S.syntax c).eval_eq_indexed_sum _ _ (S.scope c)]
  simp only [Coordinates.family, Source.family, coordinates, RationalSubstitution.IntegerBits.Family.polynomial,
    RationalSubstitution.Indexed.cleared, one_pow, mul_one]
  rfl

def context (z : List Bool) : List Bool := pairFst (pairFst z)
def innerWord (z : List Bool) : List Bool := pairFst (pairSnd z)
def outerWord (z : List Bool) : List Bool := pairSnd (pairSnd z)
theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem innerWord_FP : innerWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem outerWord_FP : outerWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def query (S : Source) (F : BivariateQueryProductBits.Family) (z : List Bool) : List Bool :=
  pair (pair (context z) (BinaryNatCode.encode (Nat.fromBitsLE (innerWord z) +
    radix S F (context z) * Nat.fromBitsLE (outerWord z)))) (pairSnd (pairFst z))

theorem query_FP (S : Source) (hS : S.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : query S F ∈ FP := by
  have hb : BinaryFn (fun z => radix S F (context z)) := (radix_binary S hS A).comp context_FP
  have hk := (BinaryFn.fromBits innerWord_FP).add (hb.mul (BinaryFn.fromBits outerWord_FP))
  exact mem_FP_pair (mem_FP_pair context_FP hk.bits_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def coefficient (S : Source) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (innerWord z) < radix S F (context z)
  then (coordinates S A).family.value (query S F z) else []

theorem evaluator (S : Source) (hS : S.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : SpaceFunction (coefficient S A) := by
  have hn := IndexedKroneckerReader.evaluator A (radix S F) (radix_binary S hS A)
  have hd := SpaceFunction.ofFP _ IndexedKroneckerReader.unitValue_FP
  have he := ((coordinates S A).evaluator hS hn hd).precompose (query S F) (query_FP S hS A)
  have hb : BinaryFn (fun z => radix S F (context z)) := (radix_binary S hS A).comp context_FP
  have hp := (BinaryFn.fromBits innerWord_FP).lt hb
  have H := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (innerWord z) < radix S F (context z)))
    hp.flag_mem_FP he (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun z => by simp only [coefficient, decide_eq_true_eq, Function.comp_apply])

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_eq (S : Source) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) (q : List Bool) (u v : ℕ) :
    coefficient S A (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      MatrixPower.residueBits ((((polynomial S F (pairFst q)).coeff v).coeff u : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  simp only [coefficient, innerWord, context, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases hu : u < radix S F (pairFst q)
  · rw [ite_eq_left hu]
    simp only [query, context, innerWord, outerWord, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, RationalSubstitution.IntegerBits.Family.value,
      RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      RationalSubstitution.IntegerBits.mValue, RationalSubstitution.IntegerBits.coefficientResidue]
    rw [coordinates_polynomial, PolynomialKronecker.coefficient _ _ (inner_lt S F _) _ _ hu]
    exact congrArg₂ (fun (a : ℤ) (n : ℕ) => MatrixPower.residueBits (a : ZMod n)) rfl
      (by simp only [pairFst_pair, pairSnd_pair])
  · rw [ite_eq_right hu, Polynomial.coeff_eq_zero_of_natDegree_lt ((inner_lt S F _ v).trans_le (by omega))]
    simp [MatrixPower.residueBits, BinaryNatCode.encode]

noncomputable def reader (S : Source) (hS : S.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) : CertifiedPolynomial.BivariateReader (polynomial S F) where
  coefficient := coefficient S A
  evaluator := evaluator S hS A
  coefficient_eq := coefficient_eq S A

end LeanCanny.ETR.BivariateTermReader
