/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveHomogeneousRowReader
public import LeanCanny.Algebra.CoerciveHomogeneousLayout

/-! # Scalar packet semantics of the native homogeneous row reader -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveHomogeneousRowParts
open LeanCanny.Encoding LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveHomogeneousRowReader
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

def packet (c : List Bool) (j r u v : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode j) (pair (BinaryNatCode.encode r)
    (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))

@[simp] theorem context_packet (c : List Bool) (j r u v : ℕ) : context (packet c j r u v) = c := by
  simp only [packet, context, pairFst_pair]
@[simp] theorem row_packet (c : List Bool) (j r u v : ℕ) : Nat.fromBitsLE (row (packet c j r u v)) = j := by
  simp only [packet, row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
@[simp] theorem rank_packet (c : List Bool) (j r u v : ℕ) : rank (packet c j r u v) = BinaryNatCode.encode r := by
  simp only [packet, rank, pairFst_pair, pairSnd_pair]
@[simp] theorem inner_packet (c : List Bool) (j r u v : ℕ) : Nat.fromBitsLE (inner (packet c j r u v)) = u := by
  simp only [packet, CoerciveHomogeneousRowReader.inner, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
@[simp] theorem outer_packet (c : List Bool) (j r u v : ℕ) : Nat.fromBitsLE (outer (packet c j r u v)) = v := by
  simp only [packet, outer, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem selected_packet (input : List Bool → List Bool) (c : List Bool)
    (j : Fin (dimension (input c))) (r u v : ℕ) :
    selected input (packet c (j.val + 1) r u v) = j.val := by
  simp only [selected, row_packet, context_packet]
  rw [min_eq_left (by omega)]
  omega

theorem target_exponent (input : List Bool → List Bool) (q : List Bool) :
    FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout (n := dimension (input (context q))))
      (CoercivePowerReaders.width (input (context q))) (Nat.fromBitsLE (target input q)) =
    FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout (n := dimension (input (context q))))
      (CoerciveHomogeneousRepack.width (input (context q))) (Nat.fromBitsLE (rank q)) := by
  exact FixedWidthPolynomial.nativeExponent_repack CoerciveCriticalHomogenization.layout
    (CoerciveHomogeneousRepack.width ∘ input ∘ context)
    (CoercivePowerReaders.width ∘ input ∘ context) rank q
    (CoerciveHomogeneousRepack.width_le (input (context q)))

theorem target_packet (input : List Bool → List Bool) (c : List Bool) (j r u v : ℕ) :
    target input (packet c j r u v) =
      CoerciveHomogeneousRepack.target input (fun _ => BinaryNatCode.encode r) c := by
  simp only [target, CoerciveHomogeneousRepack.target, FixedWidthQuery.repack,
    Function.comp_apply, context_packet]
  congr 1
  funext k
  simp only [FixedWidthQuery.entry, Function.comp_apply, context_packet, rank_packet,
    FixedWidthQuery.coordinate]

theorem target_exponent_packet (input : List Bool → List Bool) (c : List Bool) (j r u v : ℕ) :
    FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout (n := dimension (input c)))
      (CoercivePowerReaders.width (input c)) (Nat.fromBitsLE (target input (packet c j r u v))) =
    FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout (n := dimension (input c)))
      (CoerciveHomogeneousRepack.width (input c)) r := by
  generalize hq : packet c j r u v = q
  have hc : context q = c := by rw [← hq, context_packet]
  have hr : Nat.fromBitsLE (rank q) = r := by
    rw [← hq, rank_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  simpa only [hr] using target_exponent input q

noncomputable def ordinaryCoefficient (bits : List Bool) (i W r : ℕ) : ℤ :=
  if hi : i < dimension bits then
    (WeightedHomogenization.homogenize (fun _ => 1) (2 * degreeAllowance bits + 1)
      (MvPolynomial.pderiv ⟨i,hi⟩ ((polynomial bits)^2))).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout W r)
  else 0

theorem ordinary_scalar (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    CoerciveHomogeneousReaders.ordinaryValue input selected modulus (pair c (BinaryNatCode.encode r)) =
      CoerciveHomogeneousReaders.residue (ordinaryCoefficient (input c) (selected c)
        (CoercivePowerReaders.width (input c)) r) (Nat.fromBitsLE (modulus c)+1) := by
  by_cases hv : selected c < dimension (input c)
  · rw [CoerciveHomogeneousReaders.ordinary_packet input selected modulus c ⟨selected c,hv⟩ rfl r]
    simp only [ordinaryCoefficient, hv, dite_eq_left, CoerciveHomogeneousReaders.residue]
  · unfold CoerciveHomogeneousReaders.ordinaryValue HomogenizationBits.value
    split_ifs
    · rw [HomogenizationBits.oldQuery_packet, CoerciveHomogeneousReaders.derivativeReader_packet]
      simp [ordinaryCoefficient, CoerciveHomogeneousReaders.derivativeCoefficient,
        hv, CoerciveHomogeneousReaders.residue]
    · simp [ordinaryCoefficient, hv, CoerciveHomogeneousReaders.residue,
        residueBits, BinaryNatCode.encode]

theorem ordinary_packet (input modulus : List Bool → List Bool) (c : List Bool)
    (j : Fin (dimension (input c))) (r u v : ℕ) :
    ordinary input modulus (packet c (j.val + 1) r u v) = residueBits
      (((WeightedHomogenization.homogenize (fun _ => 1) (2 * degreeAllowance (input c) + 1)
        (MvPolynomial.pderiv j ((polynomial (input c)) ^ 2))).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
          (CoerciveHomogeneousRepack.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold ordinary
  rw [BinaryNat.normalize_eq_bits]
  change CoerciveHomogeneousReaders.ordinaryValue _ _ _ (pair _ (BinaryNatCode.encode _)) = _
  rw [ordinary_scalar]
  simp only [Function.comp_apply, context_packet, selected_packet]
  rw [ordinaryCoefficient, dite_eq_left j.isLt, target_exponent_packet]
  rfl

noncomputable def natResidue (a m : ℕ) : List Bool := residueBits (a : ZMod m)

theorem monomial_recontext (input modulus : List Bool → List Bool)
    (parameter power selected factor : List Bool → ℕ) (c : List Bool) (j r u v : ℕ) :
    CoerciveSparseReaders.monomialValue (input ∘ context) (target input) (modulus ∘ context)
      parameter power selected factor (packet c j r u v) =
    CoerciveSparseReaders.monomialValue input
      (CoerciveHomogeneousRepack.target input (fun _ => BinaryNatCode.encode r)) modulus
      (fun _ => parameter (packet c j r u v)) (fun _ => power (packet c j r u v))
      (fun _ => selected (packet c j r u v)) (fun _ => factor (packet c j r u v)) c := by
  unfold CoerciveSparseReaders.monomialValue
  change natResidue _ _ = natResidue _ _
  simp only [CoerciveSparseReaders.Matches, Function.comp_apply, context_packet,
    FixedWidthQuery.coordinate, target_packet]

private theorem sparse_spatial (input modulus : List Bool → List Bool) (c : List Bool)
    (j : Fin (dimension (input c))) (r N a : ℕ) :
    CoerciveSparseReaders.monomialValue input
      (CoerciveHomogeneousRepack.target input (fun _ => BinaryNatCode.encode r)) modulus
      (fun _ => 0) (fun _ => N) (fun _ => j.val) (fun _ => a) c = residueBits
      (((MvPolynomial.monomial (Finsupp.single (some j) N) (a : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
          (CoerciveHomogeneousRepack.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  rw [CoerciveSparseReaders.monomial_value_eq _ _ _ _ _ _ _ c j rfl,
    CoerciveHomogeneousRepack.exponent_eq]
  simp only [Finsupp.single_zero, zero_add, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have h := FixedWidthPolynomial.coeff_rename_rank CoerciveCriticalHomogenization.layout
    (MvPolynomial.monomial (Finsupp.single (some j) N) (a : ℤ))
    (CoerciveHomogeneousRepack.width (input c)) r
  simpa only [MvPolynomial.rename_monomial, Finsupp.mapDomain_single,
    CoerciveHomogeneousLayout.layout_some, FixedWidthPolynomial.nativeExponent_refl] using
      congrArg (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1))) h

theorem leading_packet (input modulus : List Bool → List Bool) (c : List Bool)
    (j : Fin (dimension (input c))) (r u v : ℕ) :
    leading input modulus (packet c (j.val+1) r u v) = residueBits
      (((MvPolynomial.monomial (Finsupp.single (some j) (2*degreeAllowance (input c)+1))
        ((2*degreeAllowance (input c)+2 : ℕ) : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
          (CoerciveHomogeneousRepack.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  unfold leading
  rw [monomial_recontext]
  simp only [context_packet, selected_packet]
  exact sparse_spatial input modulus c j r _ _

theorem pointCoordinate_packet (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hi : coordinate c=i.val) (j r u v : ℕ) :
    pointCoordinate input modulus coordinate (packet c j r u v) = residueBits
      (((MvPolynomial.monomial (Finsupp.single (some i) 1) (1 : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
          (CoerciveHomogeneousRepack.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  unfold pointCoordinate
  rw [monomial_recontext]
  simp only [Function.comp_apply, context_packet, hi]
  exact sparse_spatial input modulus c i r 1 1

theorem homogeneousCoordinate_packet (input modulus : List Bool → List Bool)
    (c : List Bool) (j r u v : ℕ) :
    homogeneousCoordinate input modulus (packet c j r u v) = residueBits
      (((MvPolynomial.monomial (Finsupp.single (none : Option (Fin (dimension (input c)))) 1) (1 : ℤ)).coeff
        (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
          (CoerciveHomogeneousRepack.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  unfold homogeneousCoordinate
  rw [monomial_recontext]
  unfold CoerciveSparseReaders.monomialValue
  rw [CoerciveSparseReaders.matches_parameter_iff, CoerciveHomogeneousRepack.exponent_eq]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [← FixedWidthPolynomial.coeff_rename_rank CoerciveCriticalHomogenization.layout
    (MvPolynomial.monomial (Finsupp.single (none : Option (Fin (dimension (input c)))) 1) (1 : ℤ))
    (CoerciveHomogeneousRepack.width (input c)) r]
  simp only [MvPolynomial.rename_monomial, Finsupp.mapDomain_single,
    CoerciveHomogeneousLayout.layout_none, MvPolynomial.coeff_monomial,
    FixedWidthPolynomial.nativeExponent_refl]
  split_ifs <;> simp_all [eq_comm]

end LeanCanny.ETR.CoerciveHomogeneousRowParts
