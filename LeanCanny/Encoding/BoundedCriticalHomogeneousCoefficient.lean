/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalCoefficient
public import LeanCanny.Algebra.HomogenizationSpace
public import LeanCanny.Algebra.LinearProjectionSystem

/-! # Native parameter coefficients of the homogenized critical rows -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalHomogeneousCoefficient
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra LeanCanny.Computation
open BoundedFullWriter MatrixPower RationalSubstitution.Indexed MvPolynomial Brackets FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem exponent_eq (A : ℕ) (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    exponentVector A (FixedWidthQuery.coordinate W target c) =
      nativeExponent (Equiv.refl (Fin A)) (W c) (Nat.fromBitsLE (target c)) :=
  FixedWidthCriticalBits.exponent_eq_native W target (Equiv.refl (Fin A)) c

noncomputable def polynomial (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (c : List Bool) :=
  rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize (fun _ => 1) (degree P c)
    ((BoundedCriticalSampleQuery.equations P record c (row c)).map Polynomial.C))

noncomputable def value (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (W : List Bool → ℕ)
    (k modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((((polynomial P record row (pairFst q)).coeff
    (exponentVector (P.dim (pairFst q) + 5) (entry (W (pairFst q)) (Nat.fromBitsLE (pairSnd q))))).coeff
      (Nat.fromBitsLE (k (pairFst q)))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

noncomputable def affine (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (W : List Bool → ℕ)
    (k modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (k (pairFst q)) = 0 then
    BoundedCriticalCoefficient.value (P.comp pairFst) (record ∘ pairFst) (fun p => row (pairFst p))
      (W ∘ pairFst) pairSnd (modulus ∘ pairFst) q else []

theorem affine_evaluator {P : Readers} {record : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 4)} {W : List Bool → ℕ} {k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (hk : k ∈ FP) (hm : modulus ∈ FP) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) : SpaceFunction (affine P record row W k modulus) := by
  have he := BoundedCriticalCoefficient.evaluator (row := fun p => row (pairFst p)) (h.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hr) (hi.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm) (fun p => ha (pairFst p)) (fun p => hfit (pairFst p))
  have hp := (BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP hk)).eq (BinaryFn.const 0)
  exact (SpaceFunction.branch _ hp.flag_mem_FP he (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by
      simp only [affine, decide_eq_true_eq, Function.comp_apply]
      rfl)

theorem affine_packet (P : Readers) (record : List Bool → List Bool)
    (row : (c : List Bool) → Fin (P.dim c + 4)) (W : List Bool → ℕ)
    (k modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    affine P record row W k modulus (pair c (BinaryNatCode.encode r)) =
      residueBits (((((BoundedCriticalSampleQuery.equations P record c (row c)).map Polynomial.C).coeff
        (nativeExponent (Equiv.refl (Fin (P.dim c + 4))) (W c) r)).coeff (Nat.fromBitsLE (k c)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simp only [affine, pairFst_pair, coeff_map, Polynomial.coeff_C]
  split_ifs with hk
  · have hi : (row (pairFst (pair c (BinaryNatCode.encode r)))).val = (row c).val :=
      congrArg (fun p => (row p).val) (pairFst_pair c (BinaryNatCode.encode r))
    simp only [BoundedCriticalCoefficient.value_data, Readers.comp, Function.comp_apply,
      pairFst_pair, pairSnd_pair, hi]
    rw [← BoundedCriticalCoefficient.value_data P record row (fun _ => W c)
      (fun _ => BinaryNatCode.encode r) (fun _ => modulus c) c]
    unfold BoundedCriticalCoefficient.value
    rw [exponent_eq]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · simp [residueBits, BinaryNatCode.encode]

theorem evaluator {P : Readers} {record : List Bool → List Bool}
    {row : (c : List Bool) → Fin (P.dim c + 4)} {W : List Bool → ℕ} {k modulus : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP) (hi : UnaryFn (fun c => (row c).val)) (hW : UnaryFn W)
    (hk : k ∈ FP) (hm : modulus ∈ FP) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hfit : ∀ c, degree P c < 2 ^ W c) : SpaceFunction (value P record row W k modulus) := by
  have he := HomogenizationBits.evaluator (h.dim.add (UnaryFn.const 4)) (h.dim.add (UnaryFn.const 4)) hW
    (BoundedRegularModularTerm.degree_unary h) (affine_evaluator h hr hi hW hk hm ha hfit)
  apply he.congr
  funext q
  have hp := HomogenizationBits.value_packet (fun c => P.dim c + 4) (fun c => P.dim c + 4) W (degree P)
    (affine P record row W k modulus) (pairFst q) (Equiv.refl (Fin (P.dim (pairFst q) + 4)))
    ((BoundedCriticalSampleQuery.equations P record (pairFst q) (row (pairFst q))).map Polynomial.C)
    (fun p : Polynomial ℤ => residueBits ((p.coeff (Nat.fromBitsLE (k (pairFst q)))) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [residueBits, BinaryNatCode.encode]) (fun r => affine_packet P record row W k modulus (pairFst q) r)
    (Nat.fromBitsLE (pairSnd q))
  have hq : pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) =
      pair (pairFst q) (BinaryNat.normalize (pairSnd q)) := by rw [BinaryNat.normalize_eq_bits]; rfl
  have hv : HomogenizationBits.value (fun c => P.dim c + 4) (fun c => P.dim c + 4) W (degree P)
      (affine P record row W k modulus) q =
      HomogenizationBits.value (fun c => P.dim c + 4) (fun c => P.dim c + 4) W (degree P)
        (affine P record row W k modulus) (pair (pairFst q) (BinaryNat.normalize (pairSnd q))) := by
    simp only [HomogenizationBits.value, HomogenizationBits.total, HomogenizationBits.oldQuery,
      rankTarget, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  rw [hv, ← hq, hp]
  simp only [HomogenizationLayout.prefixWeight_all]
  unfold value polynomial
  rw [FixedWidthPolynomial.coeff_rename_rank]
  rfl

end LeanCanny.Encoding.BoundedCriticalHomogeneousCoefficient
