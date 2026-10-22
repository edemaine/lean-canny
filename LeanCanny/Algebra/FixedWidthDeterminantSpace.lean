/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Polynomial-space determinant coefficients in fixed-width exponent boxes

A Kronecker substitution whose blocks fit the whole determinant turns native
multivariate entry coefficient access into univariate Berkowitz access. The
entry program rejects univariate exponents outside the finite exponent box.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A N W : List Bool → ℕ) (modulus degree : List Bool → List Bool)
variable (P : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (MvPolynomial (Fin (A c)) ℤ))

noncomputable def family : BerkowitzPolynomial.ModularFamily where
  dimension := N
  modulus c := Nat.fromBitsLE (modulus c) + 1
  degree c := Nat.fromBitsLE (degree c)
  matrix c i j := (FixedWidthKronecker.encode (A c) (W c) (P c i j)).map (Int.castRingHom _)
  modulus_ne_zero _ := by omega

def entry (coefficient : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd (pairSnd (pairSnd q))) < count (A (pairFst q)) (W (pairFst q)) then
    coefficient q else []

theorem count_mem_FP (hA : UnaryFn A) (hW : UnaryFn W) :
    (fun c => BinaryNatCode.encode (count (A c) (W c))) ∈ FP := by
  have h := FixedWidthPolynomial.countCode_mem_FP hA hW
  exact mem_FP_of_eq h (fun c => FixedWidthPolynomial.countCode_code A W c)

theorem entry_evaluator {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) : SpaceFunction (entry A W coefficient) := by
  have hd := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have hb := BinaryNat.lt_fppred hd (mem_FP_comp pairFst_mem_FP (count_mem_FP A W hA hW))
  have hb' : FPPred (fun q => Nat.fromBitsLE (pairSnd (pairSnd (pairSnd q))) < count (A (pairFst q)) (W (pairFst q))) :=
    hb.of_iff (fun q => by simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])
  have EB := SpaceFunction.branch (fun q => decide
      (Nat.fromBitsLE (pairSnd (pairSnd (pairSnd q))) < count (A (pairFst q)) (W (pairFst q))))
    hb'.flag_mem_FP E (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact EB.congr (funext fun q => by simp only [entry, decide_eq_true_eq])

noncomputable def access (coefficient : List Bool → List Bool) (D : List Bool → ℕ)
    (hP : ∀ c i j, (P c i j).totalDegree ≤ D c) (hW : ∀ c, D c < 2 ^ W c)
    (hc : ∀ c (i j : Fin (N c)) r, coefficient
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
      residueBits (((P c i j).coeff (RationalSubstitution.Indexed.exponentVector (A c) (FixedWidthPolynomial.entry (W c) r)) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1))) :
    BerkowitzPolynomial.ModularAccess (family A N W modulus degree P) where
  dimension c := BinaryNatCode.encode (N c)
  modulus c := BinaryNat.succ (modulus c)
  degree c := BinaryNat.normalize (degree c)
  entry := entry A W coefficient
  dimension_eq _ := rfl
  modulus_eq c := BinaryNat.succ_eq_bits _
  degree_eq c := BinaryNat.normalize_eq_bits _
  entry_eq c i j r := by
    change Fin (N c) at i j
    change entry A W coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) = residueBits
      (m := Nat.fromBitsLE (modulus c) + 1)
      (((FixedWidthKronecker.encode (A c) (W c) (P c i j)).map (Int.castRingHom _)).coeff r)
    have hs (m) (hm : m ∈ (P c i j).support) (k) : m k < 2 ^ W c :=
      ((MvPolynomial.monomial_le_degreeOf k hm).trans ((MvPolynomial.degreeOf_le_totalDegree _ k).trans
        (hP c i j))).trans_lt (hW c)
    simp only [entry, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode r) = r from Nat.fromBitsLE_bits r,
      Polynomial.coeff_map, Int.coe_castRingHom]
    by_cases hr : r < count (A c) (W c)
    · have hcoeff := FixedWidthKronecker.coefficient (A c) (W c) (P c i j) hs ⟨r, hr⟩
      change (FixedWidthKronecker.encode (A c) (W c) (P c i j)).coeff r = _ at hcoeff
      rw [ite_eq_left hr, hc, hcoeff, ← entry_vector (A c) (W c) ⟨r, hr⟩]
    · rw [ite_eq_right hr, FixedWidthKronecker.coefficient_of_ge (A c) (W c) _ hs r (by omega)]
      simp [residueBits, BinaryNatCode.encode]

theorem evaluator (coefficient : List Bool → List Bool) (D : List Bool → ℕ)
    (hP : ∀ c i j, (P c i j).totalDegree ≤ D c) (hW : ∀ c, D c < 2 ^ W c)
    (hc : ∀ c (i j : Fin (N c)) r, coefficient
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
      residueBits (((P c i j).coeff (RationalSubstitution.Indexed.exponentVector (A c) (FixedWidthPolynomial.entry (W c) r)) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (E : SpaceFunction coefficient) (hA : UnaryFn A) (hN : UnaryFn N) (hw : UnaryFn W)
    (hm : modulus ∈ FP) (hd : degree ∈ FP) :
    SpaceFunction (family A N W modulus degree P).value := by
  let a := access A N W modulus degree P coefficient D hP hW hc
  have hmod : (BinaryNat.succ ∘ modulus) ∈ FP := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hdegree : (BinaryNat.normalize ∘ degree) ∈ FP := mem_FP_comp hd BinaryNat.normalize_mem_FP
  have ha : a.ControlsPolyTime := ⟨bits_mem_FP hN, hmod, hdegree⟩
  exact BerkowitzPolynomial.ModularAccess.evaluator a ha (entry_evaluator A W E hA hw)

/-- The matrix dimension may be exponential; only its binary writer must be FP. -/
theorem evaluator_binary_dimension (coefficient : List Bool → List Bool) (D : List Bool → ℕ)
    (hP : ∀ c i j, (P c i j).totalDegree ≤ D c) (hW : ∀ c, D c < 2 ^ W c)
    (hc : ∀ c (i j : Fin (N c)) r, coefficient
      (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
      residueBits (((P c i j).coeff (RationalSubstitution.Indexed.exponentVector (A c) (FixedWidthPolynomial.entry (W c) r)) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (E : SpaceFunction coefficient) (hA : UnaryFn A) (hN : (fun c => BinaryNatCode.encode (N c)) ∈ FP) (hw : UnaryFn W)
    (hm : modulus ∈ FP) (hd : degree ∈ FP) :
    SpaceFunction (family A N W modulus degree P).value := by
  let a := access A N W modulus degree P coefficient D hP hW hc
  have hmod : (BinaryNat.succ ∘ modulus) ∈ FP := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hdegree : (BinaryNat.normalize ∘ degree) ∈ FP := mem_FP_comp hd BinaryNat.normalize_mem_FP
  have ha : a.ControlsPolyTime := ⟨hN, hmod, hdegree⟩
  exact BerkowitzPolynomial.ModularAccess.evaluator a ha (entry_evaluator A W E hA hw)

theorem value_eq (c : List Bool) (D : ℕ) (hD : (P c).det.totalDegree ≤ D)
    (hW : D < 2 ^ W c) (hr : Nat.fromBitsLE (degree c) < count (A c) (W c)) :
    (family A N W modulus degree P).value c =
      residueBits ((((P c).det.coeff (RationalSubstitution.Indexed.exponentVector (A c)
        (FixedWidthPolynomial.entry (W c) (Nat.fromBitsLE (degree c))))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let φ := Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))
  let ψ := (Polynomial.mapRingHom φ).comp (FixedWidthKronecker.encode (A c) (W c))
  have hs (m) (hm : m ∈ (P c).det.support) (k) : m k < 2 ^ W c :=
    ((MvPolynomial.monomial_le_degreeOf k hm).trans ((MvPolynomial.degreeOf_le_totalDegree _ k).trans hD)).trans_lt hW
  change residueBits (m := Nat.fromBitsLE (modulus c) + 1)
    ((ψ.mapMatrix (P c)).det.coeff (Nat.fromBitsLE (degree c))) = _
  rw [← ψ.map_det]
  change residueBits (m := Nat.fromBitsLE (modulus c) + 1)
    (((FixedWidthKronecker.encode (A c) (W c) (P c).det).map φ).coeff (Nat.fromBitsLE (degree c))) = _
  rw [Polynomial.coeff_map]
  have hc := FixedWidthKronecker.coefficient (A c) (W c) (P c).det hs ⟨Nat.fromBitsLE (degree c), hr⟩
  change (FixedWidthKronecker.encode (A c) (W c) (P c).det).coeff (Nat.fromBitsLE (degree c)) = _ at hc
  rw [hc, ← entry_vector (A c) (W c) ⟨Nat.fromBitsLE (degree c), hr⟩]
  rfl

end LeanCanny.Algebra.FixedWidthDeterminantBits
