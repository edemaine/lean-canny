/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleJointSource
public import LeanCanny.Algebra.CoefficientWidthBinarySpace

/-! # Critical rows in the common joint-system exponent layout

The context is `pair sourceRecord (pair spatialRow modulusMinusOne)`.
Queries attach a monomial in the common exponent width. The full-source
block reader is reused through a guarded width conversion, charging its
native computation. The bound is binary and is not an exact-degree oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open BoundedFullSampleBlock
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleBlockCritical.value
  CoefficientWidthBits.value
  BoundedFullSampleBlockCriticalSource.polynomial BoundedFullSampleBlock.width
  BoundedFullSampleBlock.degreeBound BoundedFullSampleJointSource.width

def query (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pair (pairFst (pairSnd (pairFst q)))
    (BinaryNat.normalize (pairSnd q)))) (pairSnd (pairSnd (pairFst q)))
theorem query_FP : query ∈ FP := by polytime [query]

noncomputable def source (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  BoundedFullSampleBlockCritical.value F w b bits ∘ query

theorem source_evaluator {F : Inputs} (h : F.PolyTime)
    {w b : List Bool → ℕ} (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (E : SpaceFunction bits)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (source F w b bits) :=
  (BoundedFullSampleBlockCritical.evaluator h hw hb E htP htS).precompose query query_FP

noncomputable def value (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  CoefficientWidthBits.value (fun c => F.dim (pairFst c) + 1)
    (fun c => BoundedFullSampleJointSource.width F (pairFst c))
    (fun c => BoundedFullSampleBlock.width F (pairFst c))
    (fun c => BoundedFullSampleBlock.degreeBound F (pairFst c)) (source F w b bits)

theorem evaluator {F : Inputs} (h : F.PolyTime)
    {w b : List Bool → ℕ} (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (E : SpaceFunction bits)
    (htP : ∀ c, (TermView.term (F.parent.source c)).arity ≤ F.parent.dim c)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (value F w b bits) :=
  CoefficientWidthBits.evaluator_binary_degree ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 1))
    ((BoundedFullSampleJointSource.width_unary h).comp pairFst_mem_FP)
    ((BoundedFullSampleBlock.width_unary h).comp pairFst_mem_FP)
    ((BoundedFullSampleBlock.degreeBound_binary h).comp pairFst_mem_FP)
    (source_evaluator h hw hb E htP htS)

theorem packet (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot i : Fin (F.dim u)) (hb : b u = pivot.val) (r m : ℕ) :
    value F w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode m))) (BinaryNatCode.encode r)) =
        MatrixPower.residueBits (((BoundedFullSampleBlockCriticalSource.polynomial F w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (BoundedFullSampleJointSource.width F u) r) : ℤ) : ZMod (m + 1)) := by
  let c := pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode m))
  have hc : pairFst c = u := pairFst_pair _ _
  let f : Fin (F.dim u + 1) ≃ Fin (F.dim (pairFst c) + 1) := finCongr (by rw [hc])
  have hf (j : Fin (F.dim u + 1)) : (f j).val = j.val := rfl
  have hex (V : List Bool → ℕ) (s : ℕ) : nativeExponent f (V (pairFst c)) s =
      nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (V u) s := by
    ext j
    simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm, hf, hc, Equiv.refl_apply]
  unfold value
  have H := CoefficientWidthBits.value_packet (fun c => F.dim (pairFst c) + 1)
    (fun c => BoundedFullSampleJointSource.width F (pairFst c))
    (fun c => BoundedFullSampleBlock.width F (pairFst c))
    (fun c => BoundedFullSampleBlock.degreeBound F (pairFst c))
    (source F w b bits) c f
    (BoundedFullSampleBlockCriticalSource.polynomial F w bits u pivot i)
    (fun a : ℤ => MatrixPower.residueBits (a : ZMod (m + 1))) (by rfl)
    (by rw [hc]; exact BoundedFullSampleBlock.degree_lt F u)
    (by
      intro a ha j
      rw [hc]
      exact ((MvPolynomial.monomial_le_degreeOf j ha).trans (MvPolynomial.degreeOf_le_totalDegree _ j)).trans
        (BoundedFullSampleBlockCriticalSource.polynomial_degree F w bits u pivot i))
    (by
      intro s
      rw [hex]
      have H := BoundedFullSampleBlockCritical.packet F w b bits u pivot i hb s m
      simpa only [source, Function.comp_apply, query, c, pairFst_pair, pairSnd_pair,
        BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits] using H) r
  rw [hex] at H
  exact H

end LeanCanny.Encoding.BoundedFullSampleJointCritical
