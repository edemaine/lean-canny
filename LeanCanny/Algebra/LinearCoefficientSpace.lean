/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialCoefficientSpace
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Algebra.RationalSubstitutionResidue

/-! # Streamed coefficients of a homogeneous linear polynomial

Each summand tests whether the requested exponent is its coordinate monomial,
then calls a certified scalar coefficient reader. The modular sum retains one
residue and accounts for the space-bounded scalar-reader workspace.
-/

@[expose] public section

namespace LeanCanny.Algebra.LinearCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.Indexed MatrixPower
open LeanCanny.Encoding.Brackets
open scoped BigOperators Classical

def original (p : List Bool) : List Bool := pairFst (pairFst p)
def target (p : List Bool) : List Bool := BinaryNat.normalize (pairSnd (pairFst p))

theorem original_mem_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem target_mem_FP : target ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP

def singleRead (q : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd q) = BinaryNat.normalize (pairSnd (pairFst q)) then [true] else []

theorem singleRead_mem_FP : singleRead ∈ FP :=
  (stringEq_fppred (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)).ite_mem_FP
      (constFn_mem_FP [true]) (constFn_mem_FP [])

def singleVector (A W : List Bool → ℕ) (p : List Bool) : List Bool :=
  FixedWidthNatVector.encode (A (original p)) (W (original p))
    (fun j => if j = Nat.fromBitsLE (pairSnd p) then 1 else 0)

theorem singleVector_mem_FP {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : singleVector A W ∈ FP := by
  apply FixedWidthNatVector.encode_of_coordinate (hA.comp original_mem_FP) (hW.comp original_mem_FP)
    Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary
  apply FixedWidthNatVector.coordinate_of_reader
    (e := fun p j => if j = Nat.fromBitsLE (pairSnd p) then 1 else 0) singleRead_mem_FP
  intro p j
  simp only [singleRead, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  by_cases h : j = Nat.fromBitsLE (pairSnd p)
  · simp only [h, ite_true]
    rfl
  · have hn : BinaryNatCode.encode j ≠ BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p)) :=
      fun he => h (BinaryNatCode.encode_injective he)
    simp only [BinaryNatCode.encode] at hn
    simp only [hn, ite_false, h]
    rfl

noncomputable def Matches (A W : List Bool → ℕ) : List Bool → Prop :=
  PartialCoefficientBits.EqualPrefix (A ∘ original) (W ∘ original) target (singleVector A W)

instance (A W : List Bool → ℕ) (p : List Bool) : Decidable (Matches A W p) :=
  inferInstanceAs (Decidable (PartialCoefficientBits.EqualPrefix _ _ _ _ p))

theorem matches_fppred {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : FPPred (Matches A W) :=
  PartialCoefficientBits.equalPrefix_fppred (hA.comp original_mem_FP) (hW.comp original_mem_FP)
    target_mem_FP (singleVector_mem_FP hA hW)

theorem matches_packet (A W : List Bool → ℕ) (c : List Bool) (r i : ℕ)
    (hi : i < A c) (hW : 0 < W c) :
    Matches A W (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode i)) ↔
      exponentVector (A c) (FixedWidthPolynomial.entry (W c) r) = Finsupp.single ⟨i, hi⟩ 1 := by
  have hb (j : ℕ) : (if j = i then 1 else 0) < 2 ^ W c := by
    have htwo : 1 < 2 ^ W c := Nat.one_lt_two_pow hW.ne'
    split_ifs <;> omega
  have hc (j : ℕ) (hj : j < A c) :
      FixedWidthQuery.coordinate (W ∘ original) (singleVector A W)
        (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode i)) j = if j = i then 1 else 0 := by
    simp only [FixedWidthQuery.coordinate, singleVector, original, Function.comp_apply,
      pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
    exact FixedWidthNatVector.decode_block (A c) (W c) _ j hj (hb j)
  simp only [Matches, PartialCoefficientBits.EqualPrefix, Function.comp_apply, original, pairFst_pair]
  constructor
  · intro h
    ext j
    have he := (h j.val j.isLt).trans (hc j.val j.isLt)
    simpa only [FixedWidthQuery.coordinate, target, original, Function.comp_apply, pairFst_pair,
      pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, exponentVector,
      Finsupp.coe_equivFunOnFinite_symm, FixedWidthPolynomial.entry, Finsupp.single_apply,
      Fin.ext_iff, eq_comm] using he
  · intro h j hj
    have he := congrArg (fun e => e ⟨j, hj⟩) h
    rw [hc j hj]
    simpa only [FixedWidthQuery.coordinate, target, original, Function.comp_apply, pairFst_pair,
      pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, exponentVector,
      Finsupp.coe_equivFunOnFinite_symm, FixedWidthPolynomial.entry, Finsupp.single_apply,
      Fin.ext_iff, eq_comm] using he

noncomputable def term (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ) (c : List Bool) (i : ℕ) :
    MvPolynomial (Fin (A c)) (Polynomial ℤ) :=
  if hi : i < A c then MvPolynomial.monomial (Finsupp.single ⟨i, hi⟩ 1) (a c i) else 0

noncomputable def polynomial (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    MvPolynomial (Fin (A c)) (Polynomial ℤ) := ∑ i ∈ Finset.range (A c), term A a c i

theorem polynomial_eq_sum (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    polynomial A a c = ∑ i : Fin (A c), MvPolynomial.C (a c i.val) * MvPolynomial.X i := by
  rw [polynomial, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [term, dite_eq_left i.isLt, MvPolynomial.C_mul_X_eq_monomial]

theorem homogeneous (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ) (c : List Bool) :
    (polynomial A a c).IsHomogeneous 1 := by
  rw [polynomial_eq_sum]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ (fun i _ => MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem eval {K : Type*} [CommSemiring K] (A : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (c : List Bool) (φ : Polynomial ℤ →+* K) (v : Fin (A c) → K) :
    (polynomial A a c).eval₂ φ v = ∑ i : Fin (A c), φ (a c i.val) * v i := by
  rw [polynomial_eq_sum, MvPolynomial.eval₂_sum]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]

def sourceQuery (p : List Bool) : List Bool := pair (original p) (pairSnd p)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := mem_FP_pair original_mem_FP pairSnd_mem_FP

noncomputable def summand (A W : List Bool → ℕ) (reader : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Matches A W p then reader (sourceQuery p) else []

theorem summandEvaluator {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    {reader : List Bool → List Bool} (E : SpaceFunction reader) : SpaceFunction (summand A W reader) := by
  have EC := E.precompose sourceQuery sourceQuery_mem_FP
  have ES := SpaceFunction.branch (fun p => decide (Matches A W p)) (matches_fppred hA hW).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact ES.congr (funext fun p => by simp only [summand, decide_eq_true_eq, Function.comp_apply])

theorem summand_packet (A W : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (degree modulus reader : List Bool → List Bool) (c : List Bool) (r i : ℕ)
    (hi : i < A c) (hW : 0 < W c)
    (hr : reader (pair c (BinaryNatCode.encode i)) =
      RationalSubstitution.IntegerBits.coefficientResidue ((a c i).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1)) :
    summand A W reader (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode i)) =
      RationalSubstitution.IntegerBits.coefficientResidue
        (((term A a c i).coeff (exponentVector (A c) (FixedWidthPolynomial.entry (W c) r))).coeff
          (Nat.fromBitsLE (degree c))) (Nat.fromBitsLE (modulus c) + 1) := by
  rw [summand, term, dite_eq_left hi, MvPolynomial.coeff_monomial]
  by_cases h : exponentVector (A c) (FixedWidthPolynomial.entry (W c) r) = Finsupp.single ⟨i, hi⟩ 1
  · rw [ite_eq_left ((matches_packet A W c r i hi hW).mpr h), ite_eq_left h.symm]
    simp only [sourceQuery, original, pairFst_pair, pairSnd_pair]
    exact hr
  · rw [ite_eq_right (fun hh => h ((matches_packet A W c r i hi hW).mp hh)), ite_eq_right (Ne.symm h)]
    simp [RationalSubstitution.IntegerBits.coefficientResidue, residueBits, BinaryNatCode.encode]

noncomputable def coefficient (A W : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (degree : List Bool → List Bool) (c : List Bool) (r : ℕ) : ℤ :=
  ((polynomial A a c).coeff (exponentVector (A c) (FixedWidthPolynomial.entry (W c) r))).coeff
    (Nat.fromBitsLE (degree c))

attribute [local irreducible] coefficient

noncomputable def value (A W : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (degree modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  RationalSubstitution.IntegerBits.coefficientResidue
    (coefficient A W a degree (pairFst q) (Nat.fromBitsLE (pairSnd q))) (Nat.fromBitsLE (modulus (pairFst q)) + 1)

theorem value_packet (A W : List Bool → ℕ) (a : List Bool → ℕ → Polynomial ℤ)
    (degree modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value A W a degree modulus (pair c (BinaryNatCode.encode r)) =
      RationalSubstitution.IntegerBits.coefficientResidue
        (coefficient A W a degree c r) (Nat.fromBitsLE (modulus c) + 1) := by
  simp only [value, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]

theorem evaluator {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    (hpos : ∀ c, 0 < W c) (a : List Bool → ℕ → Polynomial ℤ)
    (degree modulus reader : List Bool → List Bool) (hm : modulus ∈ FP) (E : SpaceFunction reader)
    (hr : ∀ c i, i < A c → reader (pair c (BinaryNatCode.encode i)) =
      RationalSubstitution.IntegerBits.coefficientResidue ((a c i).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1)) : SpaceFunction (value A W a degree modulus) := by
  have hc := bits_mem_FP (hA.comp pairFst_mem_FP)
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  have ES := ModularSum.evaluatorWithModulus (summandEvaluator hA hW E)
    (fun q => BinaryNatCode.encode (A (pairFst q))) (BinaryNat.succ ∘ modulus ∘ pairFst) hc hmod
    (fun q => Nat.fromBitsLE (modulus (pairFst q)) + 1)
    (by funext q; simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])
    (fun q i => ((((term A a (pairFst q) i).coeff (exponentVector (A (pairFst q))
      (FixedWidthPolynomial.entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q))))).coeff
        (Nat.fromBitsLE (degree (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by intro q; omega)
    (by
      intro q i hi
      have hi' : i < A (pairFst q) := by simpa only [MacaulayBits.fromBits_encode] using hi
      have h := summand_packet A W a degree modulus reader (pairFst q) (Nat.fromBitsLE (pairSnd q)) i hi'
        (hpos (pairFst q)) (hr (pairFst q) i hi')
      have hq : pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) =
          pair (pairFst q) (BinaryNat.normalize (pairSnd q)) := by rw [BinaryNat.normalize_eq_bits]; rfl
      rw [hq] at h
      have hm' : Matches A W (pair q (BinaryNatCode.encode i)) ↔
          Matches A W (pair (pair (pairFst q) (BinaryNat.normalize (pairSnd q))) (BinaryNatCode.encode i)) := by
        simp only [Matches, PartialCoefficientBits.EqualPrefix, Function.comp_apply, original, target,
          singleVector, FixedWidthQuery.coordinate, pairFst_pair, pairSnd_pair,
          BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
      simpa only [summand, sourceQuery, original, pairFst_pair, pairSnd_pair, hm',
        RationalSubstitution.IntegerBits.coefficientResidue] using h)
  refine ES.congr (funext fun q => ?_)
  simp only [MacaulayBits.fromBits_encode]
  simp only [value, coefficient, polynomial, MvPolynomial.coeff_sum, Polynomial.finsetSum_coeff,
    RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_sum]

end LeanCanny.Algebra.LinearCoefficientBits
