/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.BivariateTermReader
public import LeanCanny.Algebra.IndexedBivariateRationalBounds

/-! # Native bivariate coefficients of cleared rational terms

Both coordinate readers use the same radix, valid before and after clearing.
The actual encoded arithmetic source determines the even clearing width.
Specialized signs agree with the original term wherever the coordinate
denominators are nonzero, regardless of their signs or degree drops.
-/

@[expose] public section
namespace LeanCanny.ETR.BivariateRationalTermReader
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open RationalSubstitutionBits RationalSubstitution BivariateTermReader
open scoped Classical

def weight (S : Source) (c : List Bool) : ℕ := Nat.fromBitsLE (S.arity c) * (2 * (S.normalized c).length)

theorem weight_binary (S : Source) (hS : S.PolyTime) : BinaryFn (weight S) :=
  (BinaryFn.fromBits hS.arity).mul ((BinaryFn.const 2).mul (BinaryFn.ofUnary (UnaryFn.length (S.normalized_mem_FP hS))))

theorem exponent_bound (S : Source) (c : List Bool) (r i : ℕ) :
    (S.syntax c).monomialExponent r i ≤ 2 * (S.syntax c).toData.size := by
  have h := ((S.syntax c).monomialExponent_le r i).trans (S.syntax c).degreeBound_le_dataSize
  omega

noncomputable def polynomial (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) : (ℤ[X])[X] :=
  IndexedBivariate.cleared (Nat.fromBitsLE (S.arity c)) (S.syntax c).monomialCount (2 * (S.syntax c).toData.size)
    (S.syntax c).monomialCoefficient (S.syntax c).monomialExponent (N.polynomial c) (D.polynomial c)

theorem outer_degree_le (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) :
    (polynomial S N D c).natDegree ≤ weight S c * max (N.degree c) (D.degree c) := by
  rw [weight, size_eq]
  exact IndexedBivariate.outer_degree_le _ _ _ _ _ _ _ _ (fun r _ i _ => exponent_bound S c r i)
    (fun i _ => (N.polynomial_degree c i).trans (Nat.le_max_left _ _))
    (fun i _ => (D.polynomial_degree c i).trans (Nat.le_max_right _ _))

theorem inner_degree_le (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) (j : ℕ) :
    ((polynomial S N D c).coeff j).natDegree ≤ weight S c * max (N.parameterDegree c) (D.parameterDegree c) := by
  rw [weight, size_eq]
  exact IndexedBivariate.inner_degree_le _ _ _ _ _ _ _ _ (fun r _ i _ => exponent_bound S c r i)
    (fun i _ j => (N.coefficient_degree c i j).trans (Nat.le_max_left _ _))
    (fun i _ j => (D.coefficient_degree c i j).trans (Nat.le_max_right _ _)) j

def coordinateMass (N D : BivariateQueryProductBits.Family) (c : List Bool) : ℕ :=
  max (N.mass c + (N.degree c + 1).size) (D.mass c + (D.degree c + 1).size)

theorem mass_le (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) :
    NestedMass.mass (polynomial S N D c) ≤
      2 ^ (2 * (S.syntax c).toData.size + 1 + weight S c * coordinateMass N D c) := by
  have H := IndexedBivariate.mass_le (Nat.fromBitsLE (S.arity c)) (S.syntax c).monomialCount
    (2 * (S.syntax c).toData.size) (S.syntax c).toData.size (coordinateMass N D c)
    (S.syntax c).monomialCoefficient (S.syntax c).monomialExponent (N.polynomial c) (D.polynomial c)
    (fun r _ i _ => exponent_bound S c r i)
    (fun r _ => (S.syntax c).monomialCoefficient_natAbs_le_pow_dataSize r)
    (fun i _ => (NestedMass.le_pow _ _ _ (N.polynomial_degree c i) (N.coefficient_mass c i)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _)))
    (fun i _ => (NestedMass.le_pow _ _ _ (D.polynomial_degree c i) (D.coefficient_mass c i)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _)))
  apply H.trans
  apply Nat.pow_le_pow_right (by decide)
  rw [weight, size_eq]
  have h := (S.syntax c).monomialCount_size_le
  omega

def radix (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) : ℕ :=
  (weight S c + 1) * max (N.parameterDegree c) (D.parameterDegree c) + 1

theorem max_binary {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) : BinaryFn (fun c => max (f c) (g c)) :=
  (BinaryFn.ite (hf.le hg) hg hf).of_eq (fun _ => by simp only [max_def])

theorem radix_binary (S : Source) (hS : S.PolyTime) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : BinaryFn (radix S N D) :=
  (((weight_binary S hS).add (BinaryFn.const 1)).mul (max_binary A.parameterDegree_binary B.parameterDegree_binary)).add (BinaryFn.const 1)

theorem numerator_inner_lt (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) :
    N.parameterDegree c < radix S N D c := by
  have h := Nat.le_max_left (N.parameterDegree c) (D.parameterDegree c)
  unfold radix
  nlinarith

theorem denominator_inner_lt (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) :
    D.parameterDegree c < radix S N D c := by
  have h := Nat.le_max_right (N.parameterDegree c) (D.parameterDegree c)
  unfold radix
  nlinarith

theorem inner_lt (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) (j : ℕ) :
    ((polynomial S N D c).coeff j).natDegree < radix S N D c := by
  apply (inner_degree_le S N D c j).trans_lt
  unfold radix
  rw [Nat.add_mul, Nat.one_mul]
  omega

noncomputable def coordinates (S : Source) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : Coordinates S where
  numerator c i := PolynomialKronecker.encode (radix S N D c) (N.polynomial c i)
  denominator c i := PolynomialKronecker.encode (radix S N D c) (D.polynomial c i)
  numeratorCode := IndexedKroneckerReader.value A (radix S N D)
  denominatorCode := IndexedKroneckerReader.value B (radix S N D)
  numerator_eq c i _ k m hm := IndexedKroneckerReader.packet A _ (numerator_inner_lt S N D) c i k m hm
  denominator_eq c i _ k m hm := IndexedKroneckerReader.packet B _ (denominator_inner_lt S N D) c i k m hm

theorem coordinates_polynomial (S : Source) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) (c : List Bool) :
    (coordinates S A B).family.polynomial c = PolynomialKronecker.encode (radix S N D c) (polynomial S N D c) := by
  rw [polynomial, IndexedBivariate.encode_cleared]
  rfl

def query (S : Source) (N D : BivariateQueryProductBits.Family) (z : List Bool) : List Bool :=
  pair (pair (context z) (BinaryNatCode.encode (Nat.fromBitsLE (innerWord z) +
    radix S N D (context z) * Nat.fromBitsLE (outerWord z)))) (pairSnd (pairFst z))

theorem query_FP (S : Source) (hS : S.PolyTime) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : query S N D ∈ FP := by
  have hb : BinaryFn (fun z => radix S N D (context z)) := (radix_binary S hS A B).comp context_FP
  have hk := (BinaryFn.fromBits innerWord_FP).add (hb.mul (BinaryFn.fromBits outerWord_FP))
  exact mem_FP_pair (mem_FP_pair context_FP hk.bits_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def coefficient (S : Source) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (innerWord z) < radix S N D (context z)
  then (coordinates S A B).family.value (query S N D z) else []

theorem evaluator (S : Source) (hS : S.PolyTime) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : SpaceFunction (coefficient S A B) := by
  have hn := IndexedKroneckerReader.evaluator A (radix S N D) (radix_binary S hS A B)
  have hd := IndexedKroneckerReader.evaluator B (radix S N D) (radix_binary S hS A B)
  have he := ((coordinates S A B).evaluator hS hn hd).precompose (query S N D) (query_FP S hS A B)
  have hb : BinaryFn (fun z => radix S N D (context z)) := (radix_binary S hS A B).comp context_FP
  have hp := (BinaryFn.fromBits innerWord_FP).lt hb
  have H := SpaceFunction.branch (fun z => decide (Nat.fromBitsLE (innerWord z) < radix S N D (context z)))
    hp.flag_mem_FP he (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun z => by simp only [coefficient, decide_eq_true_eq, Function.comp_apply])

set_option backward.isDefEq.respectTransparency false in
theorem coefficient_eq (S : Source) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) (q : List Bool) (u v : ℕ) :
    coefficient S A B (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      MatrixPower.residueBits ((((polynomial S N D (pairFst q)).coeff v).coeff u : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  simp only [coefficient, innerWord, context, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases hu : u < radix S N D (pairFst q)
  · rw [ite_eq_left hu]
    simp only [query, context, innerWord, outerWord, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, RationalSubstitution.IntegerBits.Family.value,
      RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
      RationalSubstitution.IntegerBits.mValue, RationalSubstitution.IntegerBits.coefficientResidue]
    rw [coordinates_polynomial, PolynomialKronecker.coefficient _ _ (inner_lt S N D _) _ _ hu]
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => MatrixPower.residueBits (a : ZMod m)) rfl
      (by simp only [pairFst_pair, pairSnd_pair])
  · rw [ite_eq_right hu, Polynomial.coeff_eq_zero_of_natDegree_lt ((inner_lt S N D _ v).trans_le (by omega))]
    simp [MatrixPower.residueBits, BinaryNatCode.encode]

noncomputable def reader (S : Source) (hS : S.PolyTime) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) :
    CertifiedPolynomial.BivariateReader (polynomial S N D) where
  coefficient := coefficient S A B
  evaluator := evaluator S hS A B
  coefficient_eq := coefficient_eq S A B

noncomputable def environment (N D : BivariateQueryProductBits.Family) (c : List Bool) (β x : ℝ) : ℕ → ℝ :=
  fun i => ((N.polynomial c i).map (ParameterTarski.evalHom β)).eval x /
    ((D.polynomial c i).map (ParameterTarski.evalHom β)).eval x

theorem sign_specialize (S : Source) (N D : BivariateQueryProductBits.Family) (c : List Bool) (β x : ℝ)
    (hd : ∀ i, i < Nat.fromBitsLE (S.arity c) → ((D.polynomial c i).map (ParameterTarski.evalHom β)).eval x ≠ 0) :
    SignType.sign (((polynomial S N D c).map (ParameterTarski.evalHom β)).eval x) =
      SignType.sign ((S.syntax c).eval (environment N D c β x)) := by
  rw [polynomial, IndexedBivariate.specialize]
  have H := Indexed.sign_eval₂_cleared (RingHom.id ℝ) x (Nat.fromBitsLE (S.arity c)) (S.syntax c).monomialCount (S.syntax c).toData.size
    (fun r => ((S.syntax c).monomialCoefficient r : ℝ)) (S.syntax c).monomialExponent
    (fun i => (N.polynomial c i).map (ParameterTarski.evalHom β))
    (fun i => (D.polynomial c i).map (ParameterTarski.evalHom β))
    (fun r _ i _ => exponent_bound S c r i) hd
  change SignType.sign _ = SignType.sign ((Indexed.source (Nat.fromBitsLE (S.arity c))
    (S.syntax c).monomialCount (fun r => ((S.syntax c).monomialCoefficient r : ℝ)) (S.syntax c).monomialExponent).eval₂
      (RingHom.id ℝ) (fun i => environment N D c β x i.val)) at H
  rw [Indexed.eval₂_source] at H
  change SignType.sign _ = SignType.sign (∑ r ∈ Finset.range (S.syntax c).monomialCount,
    ((S.syntax c).monomialCoefficient r : ℝ) * ∏ i ∈ Finset.range (Nat.fromBitsLE (S.arity c)),
      environment N D c β x i ^ (S.syntax c).monomialExponent r i) at H
  rw [← (S.syntax c).eval_eq_indexed_sum _ _ (S.scope c)] at H
  exact H

end LeanCanny.ETR.BivariateRationalTermReader
