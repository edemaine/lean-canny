/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace
public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Encoding.SuppliedFrozenMaskFP
/-! # Native exponent repacking for spatial coordinate permutations

Only exponent blocks are permuted. The source word, its large coefficients,
and the complete caller context stay unchanged. Arbitrary indices are handled
by the existing bounded fixed-width reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthPermutationBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.Indexed
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A W : List Bool → ℕ) (target inverse : List Bool → List Bool)

def indexQuery (p : List Bool) : List Bool := pair (pairFst p) (inverse p)
def read (p : List Bool) : List Bool := FixedWidthQuery.read A W target (indexQuery inverse p)
def coordinate (c : List Bool) (i : ℕ) : ℕ :=
  FixedWidthQuery.entry A W target c (Nat.fromBitsLE (inverse (pair c (BinaryNatCode.encode i))))
def word (c : List Bool) : List Bool := FixedWidthNatVector.encode (A c) (W c) (coordinate A W target inverse c)

theorem read_FP (hA : UnaryFn A) (hW : UnaryFn W) (ht : target∈FP) (hi : inverse∈FP) : read A W target inverse∈FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP hi) (FixedWidthQuery.read_mem_FP hA hW ht)

theorem read_packet (c : List Bool) (i : ℕ) :
    read A W target inverse (pair c (BinaryNatCode.encode i))=BinaryNatCode.encode (coordinate A W target inverse c i) := by
  unfold read indexQuery coordinate
  rw [pairFst_pair]
  have H := FixedWidthQuery.read_packet A W target c
    (Nat.fromBitsLE (inverse (pair c (BinaryNatCode.encode i))))
  simp only [FixedWidthQuery.read, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] at H ⊢
  exact H

theorem word_FP (hA : UnaryFn A) (hW : UnaryFn W) (ht : target∈FP) (hi : inverse∈FP) : word A W target inverse∈FP :=
  FixedWidthNatVector.encode_mem_FP A W _ hA hW (read A W target inverse)
    (read_FP A W target inverse hA hW ht hi) (read_packet A W target inverse)

theorem word_coordinate (c : List Bool) (i : ℕ) (hi : i<A c) :
    FixedWidthQuery.coordinate W (word A W target inverse) c i=coordinate A W target inverse c i := by
  apply FixedWidthNatVector.decode_block _ _ _ i hi
  unfold coordinate FixedWidthQuery.entry FixedWidthQuery.coordinate
  split_ifs
  · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  · exact Nat.two_pow_pos _

theorem exponent_word (c : List Bool) (ρ : Equiv.Perm (Fin (A c)))
    (hi : ∀ i : Fin (A c), inverse (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (ρ.symm i).val) :
    exponentVector (A c) (FixedWidthQuery.coordinate W (word A W target inverse) c)=
      (exponentVector (A c) (FixedWidthQuery.coordinate W target c)).mapDomain ρ := by
  ext i
  simp only [exponentVector,Finsupp.coe_equivFunOnFinite_symm,Finsupp.mapDomain_equiv_apply]
  rw [word_coordinate A W target inverse c i.val i.isLt]
  unfold coordinate
  rw [hi i]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,FixedWidthQuery.entry,ite_eq_left (ρ.symm i).isLt]

theorem coefficient (c : List Bool) (ρ : Equiv.Perm (Fin (A c)))
    (hi : ∀ i : Fin (A c), inverse (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (ρ.symm i).val)
    (p : MvPolynomial (Fin (A c)) ℤ) :
    p.coeff (exponentVector (A c) (FixedWidthQuery.coordinate W (word A W target inverse) c))=
      (MvPolynomial.rename ρ.symm p).coeff (exponentVector (A c) (FixedWidthQuery.coordinate W target c)) := by
  rw [exponent_word A W target inverse c ρ hi]
  have H : ((exponentVector (A c) (FixedWidthQuery.coordinate W target c)).mapDomain ρ).mapDomain ρ.symm=
      exponentVector (A c) (FixedWidthQuery.coordinate W target c) := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
  calc
    _ = (MvPolynomial.rename ρ.symm p).coeff (((exponentVector (A c)
        (FixedWidthQuery.coordinate W target c)).mapDomain ρ).mapDomain ρ.symm) :=
      (MvPolynomial.coeff_rename_mapDomain ρ.symm ρ.symm.injective p _).symm
    _ = _ := congrArg (fun d => (MvPolynomial.rename ρ.symm p).coeff d) H

/-- The concrete inverse reader for frozen-first ordering keeps the saved key. -/
def frozenInverse (mask : List Bool → List Bool) (p : List Bool) : List Bool :=
  SuppliedFrozenMaskBits.inverse (A (pairFst p)) (mask (pairFst p)) (Nat.fromBitsLE (pairSnd p))

theorem frozenInverse_FP (hA : UnaryFn A) (mask : List Bool → List Bool) (hm : mask∈FP) :
    frozenInverse A mask∈FP :=
  SuppliedFrozenMaskBits.inverse_FP _ hA.lift _ (mem_FP_comp pairFst_mem_FP hm) _ (BinaryFn.fromBits pairSnd_mem_FP)

theorem frozenInverse_packet (mask : List Bool → List Bool) (c : List Bool) (i : Fin (A c)) :
    frozenInverse A mask (pair c (BinaryNatCode.encode i.val))=
      BinaryNatCode.encode ((LeanCanny.Geometry.FrozenCoordinateOrdering.permutation (SuppliedFrozenMaskBits.selected (A c) (mask c))).symm i).val := by
  simp only [frozenInverse,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact SuppliedFrozenMaskBits.inverse_packet _ _ i
end LeanCanny.Algebra.FixedWidthPermutationBits
