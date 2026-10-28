/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentFullBlockPolynomial
public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Total native exponent queries for actual-sample coordinate blocks

Critical-equation readers query exponent vectors by arbitrary binary words.
Repacking keeps exactly the declared variable blocks before invoking the
collected coefficient reader. High unused blocks cannot change the monomial.
The parameter remains variable zero; all other variables are spatial.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentFullBlockCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FixedWidthPolynomial RationalParentFullBlock
open scoped Classical
attribute [local irreducible] RationalParentFullBlock.width

noncomputable def packed (F : Inputs) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun z => F.dim (pairFst z) + 1) (fun z => width F (pairFst z))
    (fun z => F.dim (pairFst z) + 1) (fun z => width F (pairFst z)) pairSnd

theorem packed_FP {F : Inputs} (h : F.Access) : packed F ∈ FP :=
  FixedWidthQuery.repack_mem_FP ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((width_unary h).comp pairFst_mem_FP) ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((width_unary h).comp pairFst_mem_FP) pairSnd_mem_FP

noncomputable def query (F : Inputs) (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNat.normalize (packed F (pairFst q)))) (pairSnd q)

theorem query_FP {F : Inputs} (h : F.Access) : query F ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP (packed_FP h)) BinaryNat.normalize_mem_FP)) pairSnd_mem_FP

noncomputable def value (F : Inputs) : List Bool → List Bool :=
  RationalParentFullBlockPolynomial.coefficient F ∘ query F

theorem evaluator {F : Inputs} (h : F.Access)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (value F) :=
  (RationalParentFullBlockPolynomial.evaluator h htS).precompose (query F) (query_FP h)

theorem packed_bound (F : Inputs) (u : List Bool) (r : ℕ) :
    Nat.fromBitsLE (packed F (pair u (BinaryNatCode.encode r))) < count (F.dim u + 1) (width F u) := by
  have H := Nat.fromBitsLE_lt_pow_length (packed F (pair u (BinaryNatCode.encode r)))
  simpa only [packed, FixedWidthQuery.repack_length, pairFst_pair, count, ← pow_mul,
    Nat.mul_comm (width F u)] using H

theorem packed_exponent (F : Inputs) (u : List Bool) (r : ℕ) :
    nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (width F u)
      (Nat.fromBitsLE (packed F (pair u (BinaryNatCode.encode r)))) =
        nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (width F u) r := by
  have hp : packed F (pair u (BinaryNatCode.encode r)) =
      FixedWidthNatVector.encode (F.dim u + 1) (width F u)
        (fun i => if i < F.dim u + 1 then entry (width F u) r i else 0) := by
    simp only [packed, FixedWidthQuery.repack, pairFst_pair]
    apply congrArg (FixedWidthNatVector.encode (F.dim u + 1) (width F u))
    funext i
    simp only [FixedWidthQuery.entry, FixedWidthQuery.coordinate, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, entry]
  ext i
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply]
  have he (bits : List Bool) : entry (width F u) (Nat.fromBitsLE bits) i.val =
      Nat.fromBitsLE ((bits.drop (i.val * width F u)).take (width F u)) := by
    rw [entry_eq_digit, BinaryNat.value_take, drop_value]
  rw [he, hp, FixedWidthNatVector.decode_block _ _ _ i.val i.isLt (by
    rw [ite_eq_left i.isLt]
    exact entry_lt _ _ _), ite_eq_left i.isLt]

theorem packet (F : Inputs) (u : List Bool)
    (r m : ℕ) (hm : 0 < m) :
    value F (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((RationalParentFullBlockPolynomial.polynomial F u).coeff
        (nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (width F u) r) : ℤ) : ZMod m) := by
  let s := Nat.fromBitsLE (packed F (pair u (BinaryNatCode.encode r)))
  have hs : s < count (F.dim u + 1) (width F u) := packed_bound F u r
  have H := RationalParentFullBlockPolynomial.coefficient_packet F u ⟨s, hs⟩ m hm
  simp only [value, Function.comp_apply, query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
  change RationalParentFullBlockPolynomial.coefficient F
    (pair (pair u (BinaryNatCode.encode s)) (BinaryNatCode.encode (m - 1))) = _
  rw [H, ← entry_vector, ← nativeExponent_refl, packed_exponent]

end LeanCanny.Encoding.RationalParentFullBlockCoefficient
