/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockTerm
public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Total native exponent queries for actual-sample coordinate blocks

Critical-equation readers query exponent vectors by arbitrary binary words.
Repacking keeps exactly the declared variable blocks before invoking the
collected coefficient reader. High unused blocks cannot change the monomial.
The parameter remains variable zero; all other variables are spatial.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FixedWidthPolynomial BoundedCriticalSampleBlockEncoding
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleBlockEncoding.width

noncomputable def packed (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun z => k (pairFst z) + 1) (fun z => width P read (pairFst z))
    (fun z => k (pairFst z) + 1) (fun z => width P read (pairFst z)) pairSnd

theorem packed_FP {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : packed P read k ∈ FP :=
  FixedWidthQuery.repack_mem_FP ((hk.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((width_unary h read hr).comp pairFst_mem_FP) ((hk.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((width_unary h read hr).comp pairFst_mem_FP) pairSnd_mem_FP

noncomputable def query (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNat.normalize (packed P read k (pairFst q)))) (pairSnd q)

theorem query_FP {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : query P read k ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP (packed_FP h read hr hk)) BinaryNat.normalize_mem_FP)) pairSnd_mem_FP

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) : List Bool → List Bool :=
  BoundedCriticalSampleBlockTerm.coefficient P read o k ∘ query P read k

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P read o k) :=
  (BoundedCriticalSampleBlockTerm.evaluator h read hr ho hk ha).precompose (query P read k) (query_FP h read hr hk)

theorem packed_bound (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) (r : ℕ) :
    Nat.fromBitsLE (packed P read k (pair u (BinaryNatCode.encode r))) < count (k u + 1) (width P read u) := by
  have H := Nat.fromBitsLE_lt_pow_length (packed P read k (pair u (BinaryNatCode.encode r)))
  simpa only [packed, FixedWidthQuery.repack_length, pairFst_pair, count, ← pow_mul,
    Nat.mul_comm (width P read u)] using H

theorem packed_exponent (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) (r : ℕ) :
    nativeExponent (Equiv.refl (Fin (k u + 1))) (width P read u)
      (Nat.fromBitsLE (packed P read k (pair u (BinaryNatCode.encode r)))) =
        nativeExponent (Equiv.refl (Fin (k u + 1))) (width P read u) r := by
  have hp : packed P read k (pair u (BinaryNatCode.encode r)) =
      FixedWidthNatVector.encode (k u + 1) (width P read u)
        (fun i => if i < k u + 1 then entry (width P read u) r i else 0) := by
    simp only [packed, FixedWidthQuery.repack, pairFst_pair]
    apply congrArg (FixedWidthNatVector.encode (k u + 1) (width P read u))
    funext i
    simp only [FixedWidthQuery.entry, FixedWidthQuery.coordinate, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, entry]
  ext i
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply]
  have he (bits : List Bool) : entry (width P read u) (Nat.fromBitsLE bits) i.val =
      Nat.fromBitsLE ((bits.drop (i.val * width P read u)).take (width P read u)) := by
    rw [entry_eq_digit, BinaryNat.value_take, drop_value]
  rw [he, hp, FixedWidthNatVector.decode_block _ _ _ i.val i.isLt (by
    rw [ite_eq_left i.isLt]
    exact entry_lt _ _ _), ite_eq_left i.isLt]

theorem packet (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (u : List Bool)
    (r m : ℕ) (hm : 0 < m) :
    value P read o k (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((BoundedCriticalSampleBlockTerm.polynomial P read o k u).coeff
        (nativeExponent (Equiv.refl (Fin (k u + 1))) (width P read u) r) : ℤ) : ZMod m) := by
  let s := Nat.fromBitsLE (packed P read k (pair u (BinaryNatCode.encode r)))
  have hs : s < count (k u + 1) (width P read u) := packed_bound P read k u r
  have H := BoundedCriticalSampleBlockTerm.coefficient_packet P read o k u ⟨s, hs⟩ m hm
  simp only [value, Function.comp_apply, query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits]
  change BoundedCriticalSampleBlockTerm.coefficient P read o k
    (pair (pair u (BinaryNatCode.encode s)) (BinaryNatCode.encode (m - 1))) = _
  rw [H, ← entry_vector, ← nativeExponent_refl, packed_exponent]

end LeanCanny.Encoding.BoundedCriticalSampleBlockCoefficient
