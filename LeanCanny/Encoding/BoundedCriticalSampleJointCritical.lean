/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointSource
public import LeanCanny.Algebra.CoefficientWidthBinarySpace

/-! # Critical rows in the common joint-system exponent layout

The context is `pair sourceRecord (pair spatialRow modulusMinusOne)`.
Queries attach a monomial in the common exponent width. The old block reader
is reused through a guarded width conversion, charging its original native
computation. The bound is binary and is not an exact-degree oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleBlockCritical.value
  CoefficientWidthBits.value
  BoundedCriticalSampleBlockCriticalSource.polynomial BoundedCriticalSampleBlockEncoding.width
  BoundedCriticalSampleBlockEncoding.budget BoundedCriticalSampleJointSource.width

def query (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pair (pairFst (pairSnd (pairFst q)))
    (BinaryNat.normalize (pairSnd q)))) (pairSnd (pairSnd (pairFst q)))
theorem query_FP : query ∈ FP := by polytime [query]

noncomputable def source (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  BoundedCriticalSampleBlockCritical.value P read o k w b bits ∘ query

theorem source_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w b : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P read o k w b bits) :=
  (BoundedCriticalSampleBlockCritical.evaluator h read hr ho hk hw hb hbits ha).precompose query query_FP

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  CoefficientWidthBits.value (fun c => k (pairFst c) + 1)
    (fun c => BoundedCriticalSampleJointSource.width P read (pairFst c))
    (fun c => BoundedCriticalSampleBlockEncoding.width P read (pairFst c))
    (fun c => BoundedCriticalSampleBlockEncoding.budget P read (pairFst c)) (source P read o k w b bits)

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w b : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P read o k w b bits) :=
  CoefficientWidthBits.evaluator_binary_degree ((hk.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((BoundedCriticalSampleJointSource.width_unary h read hr).comp pairFst_mem_FP)
    ((BoundedCriticalSampleBlockEncoding.width_unary h read hr).comp pairFst_mem_FP)
    ((BoundedCriticalSampleBlockEncoding.budget_binary h read hr).comp pairFst_mem_FP)
    (source_evaluator h read hr ho hk hw hb hbits ha)

theorem packet (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot i : Fin (k u)) (hb : b u = pivot.val) (r m : ℕ) :
    value P read o k w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode m))) (BinaryNatCode.encode r)) =
        MatrixPower.residueBits (((BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleJointSource.width P read u) r) : ℤ) : ZMod (m + 1)) := by
  let c := pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode m))
  have hc : pairFst c = u := pairFst_pair _ _
  let f : Fin (k u + 1) ≃ Fin (k (pairFst c) + 1) := finCongr (by rw [hc])
  have hf (j : Fin (k u + 1)) : (f j).val = j.val := rfl
  have hex (V : List Bool → ℕ) (s : ℕ) : nativeExponent f (V (pairFst c)) s =
      nativeExponent (Equiv.refl (Fin (k u + 1))) (V u) s := by
    ext j
    simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, hf, hc, Equiv.refl_apply]
  unfold value
  have H := CoefficientWidthBits.value_packet (fun c => k (pairFst c) + 1)
    (fun c => BoundedCriticalSampleJointSource.width P read (pairFst c))
    (fun c => BoundedCriticalSampleBlockEncoding.width P read (pairFst c))
    (fun c => BoundedCriticalSampleBlockEncoding.budget P read (pairFst c))
    (source P read o k w b bits) c f
    (BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits u pivot i)
    (fun a : ℤ => MatrixPower.residueBits (a : ZMod (m + 1))) (by rfl)
    (by rw [hc]; unfold BoundedCriticalSampleBlockEncoding.width; exact Nat.lt_size_self _)
    (by
      intro a ha j
      rw [hc]
      exact ((MvPolynomial.monomial_le_degreeOf j ha).trans (MvPolynomial.degreeOf_le_totalDegree _ j)).trans
        (BoundedCriticalSampleBlockCriticalSource.polynomial_degree P read o k w bits u pivot i))
    (by
      intro s
      rw [hex]
      have H := BoundedCriticalSampleBlockCritical.packet P read o k w b bits u pivot i hb s m
      simpa only [source, Function.comp_apply, query, c, pairFst_pair, pairSnd_pair,
        BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H) r
  rw [hex] at H
  exact H

end LeanCanny.Encoding.BoundedCriticalSampleJointCritical
