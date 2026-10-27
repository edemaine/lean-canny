/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockCoefficient
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalSource

/-! # Native critical-equation coefficients over actual-sample blocks

A request is `pair (pair sourceRecord (pair row monomial)) modulusMinusOne`.
The row and pivot name free block coordinates; variable zero stays the sample
parameter. Native derivative calls and modular arithmetic construct each
critical equation directly from the original block coefficients. Invalid
rows or pivots return zero, including empty spatial blocks.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FixedWidthPolynomial BoundedCriticalSampleBlockEncoding
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleBlockTerm.polynomial
  BoundedCriticalSampleBlockCoefficient.value FixedWidthCriticalBits.value width budget

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def row (q : List Bool) : List Bool := pairFst (pairSnd (pairFst q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairFst q))
def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem row_FP : row ∈ FP := by polytime [row]
theorem target_FP : target ∈ FP := by polytime [target]
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

def sourceQuery (q : List Bool) : List Bool :=
  pair (pair (origin (pairFst q)) (BinaryNat.normalize (pairSnd q))) (BinaryNat.normalize (pairSnd (pairFst q)))
theorem sourceQuery_FP : sourceQuery ∈ FP := by
  have hc : (fun q => origin (pairFst q)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := origin) pairFst_mem_FP origin_FP
  exact mem_FP_pair (mem_FP_pair hc (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP))
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)

noncomputable def source (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) : List Bool → List Bool :=
  BoundedCriticalSampleBlockCoefficient.value P read o k ∘ sourceQuery

theorem source_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P read o k) :=
  (BoundedCriticalSampleBlockCoefficient.evaluator h read hr ho hk ha).precompose sourceQuery sourceQuery_FP

theorem source_packet (P : Readers) (read : List Bool → List Bool) (o k : List Bool → ℕ) (q : List Bool) (s : ℕ) :
    source P read o k (pair q (BinaryNatCode.encode s)) = MatrixPower.residueBits
      (((BoundedCriticalSampleBlockTerm.polynomial P read o k (origin q)).coeff
        (nativeExponent (Equiv.refl (Fin (k (origin q) + 1))) (width P read (origin q)) s) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have H := BoundedCriticalSampleBlockCoefficient.packet P read o k (origin q) s
    (Nat.fromBitsLE (pairSnd q) + 1) (by omega)
  simpa only [source, Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel] using H

def directionQuery (q : List Bool) : List Bool := pair (origin q) (BinaryNat.normalize (row q))
theorem directionQuery_FP : directionQuery ∈ FP :=
  mem_FP_pair origin_FP (mem_FP_comp row_FP BinaryNat.normalize_mem_FP)

def direction (k w : List Bool → ℕ) (bits : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.read k w bits ∘ directionQuery
theorem direction_FP {k w : List Bool → ℕ} (hk : UnaryFn k) (hw : UnaryFn w)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP) : direction k w bits ∈ FP :=
  mem_FP_comp directionQuery_FP (FixedWidthQuery.read_mem_FP hk hw hbits)

def base (k b : List Bool → ℕ) (q : List Bool) : ℕ := min (b (origin q)) (k (origin q)) + 1
def selected (k : List Bool → ℕ) (q : List Bool) : ℕ := min (Nat.fromBitsLE (row q)) (k (origin q)) + 1
theorem base_unary {k b : List Bool → ℕ} (hk : UnaryFn k) (hb : BinaryFn b) : UnaryFn (base k b) := by
  have B : BinaryFn (fun q => b (origin q)) := hb.comp origin_FP
  exact ((UnaryFn.fromBitsLE_min B.bits_mem_FP (hk.comp origin_FP)).of_eq (fun q => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits])).add (UnaryFn.const 1)
theorem selected_unary {k : List Bool → ℕ} (hk : UnaryFn k) : UnaryFn (selected k) :=
  (UnaryFn.fromBitsLE_min row_FP (hk.comp origin_FP)).add (UnaryFn.const 1)

def valid (k b : List Bool → ℕ) (q : List Bool) : Prop :=
  b (origin q) < k (origin q) ∧ Nat.fromBitsLE (row q) < k (origin q)
instance (k b : List Bool → ℕ) (q : List Bool) : Decidable (valid k b q) := inferInstanceAs (Decidable (_ ∧ _))
theorem valid_pred {k b : List Bool → ℕ} (hk : UnaryFn k) (hb : BinaryFn b) : FPPred (valid k b) := by
  have K : BinaryFn (fun q => k (origin q)) := BinaryFn.ofUnary (hk.comp origin_FP)
  have B : BinaryFn (fun q => b (origin q)) := hb.comp origin_FP
  exact (B.lt K).and ((BinaryFn.fromBits row_FP).lt K)

noncomputable def raw (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthCriticalBits.value (fun q => k (origin q) + 1) (fun q => width P read (origin q))
    (fun q => budget P read (origin q)) (base k b) (selected k) target modulus (direction k w bits) (source P read o k)

theorem raw_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w b : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (raw P read o k w b bits) :=
  FixedWidthCriticalBits.evaluator _ _ _ _ _ _ _ _ (source_evaluator h read hr ho hk ha)
    ((hk.comp origin_FP).add (UnaryFn.const 1)) ((width_unary h read hr).comp origin_FP)
    ((budget_binary h read hr).comp origin_FP) (base_unary hk hb) (selected_unary hk)
    target_FP modulus_FP (direction_FP hk hw hbits)

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) : List Bool :=
  if valid k b q then raw P read o k w b bits q else []

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w b : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P read o k w b bits) := by
  exact (SpaceFunction.branch (fun q => decide (valid k b q)) (valid_pred hk hb).flag_mem_FP
    (raw_evaluator h read hr ho hk hw hb hbits ha) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq])

theorem packet (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot i : Fin (k u)) (hb : b u = pivot.val) (r m : ℕ) :
    value P read o k w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
        MatrixPower.residueBits (((BoundedCriticalSampleBlockCriticalSource.polynomial P read o k w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (k u + 1))) (width P read u) r) : ℤ) : ZMod (m + 1)) := by
  let q := pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)
  have hq : origin q = u := by simp only [q, origin, pairFst_pair]
  have hr : Nat.fromBitsLE (row q) = i.val := by
    simp only [q, row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have ht : Nat.fromBitsLE (target q) = r := by
    simp only [q, target, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hm : Nat.fromBitsLE (pairSnd q) = m := by
    simp only [q, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hdirection : direction k w bits q =
      BinaryNatCode.encode (BoundedCriticalSampleBlockCriticalSource.direction k w bits u i) := by
    have hrow : BinaryNat.normalize (row q) = BinaryNatCode.encode i.val := by
      simp only [BinaryNat.normalize_eq_bits, hr, BinaryNatCode.encode]
    rw [direction, Function.comp_apply, directionQuery, hq, hrow]
    exact FixedWidthQuery.read_packet k w bits u i.val
  have hv : valid k b q := by
    change b (origin q) < k (origin q) ∧ Nat.fromBitsLE (row q) < k (origin q)
    rw [hq, hr, hb]
    exact ⟨pivot.isLt, i.isLt⟩
  have H := FixedWidthCriticalBits.packet (fun z => k (origin z) + 1) (fun z => width P read (origin z))
    (fun z => budget P read (origin z)) (base k b) (selected k) target modulus (direction k w bits)
    (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleBlockTerm.polynomial P read o k u) pivot.succ i.succ
    (BoundedCriticalSampleBlockCriticalSource.direction k w bits u i) m (source P read o k) q
    (by rw [hq]) (by simp only [base, hq, hb, Nat.min_eq_left pivot.isLt.le]; rfl)
    (by simp only [selected, hr, hq, Nat.min_eq_left i.isLt.le]; rfl)
    (by unfold budget; omega) (by rw [hq]; exact BoundedCriticalSampleBlockCriticalSource.source_degree P read o k u)
    (by rw [hq]; unfold width; exact Nat.lt_size_self _)
    (by simp only [modulus, BinaryNat.succ_eq_bits, hm, BinaryNatCode.encode]) hdirection
    (by
      intro s
      have hs := source_packet P read o k q s
      have hc := congrArg (fun v => (BoundedCriticalSampleBlockTerm.polynomial P read o k v).coeff
        (nativeExponent (Equiv.refl (Fin (k v + 1))) (width P read v) s)) hq
      rw [hc, hm] at hs
      simpa only [hq] using hs)
  change (if valid k b q then raw P read o k w b bits q else []) = _
  rw [ite_eq_left hv]
  simpa only [raw, hq, ht,
    BoundedCriticalSampleBlockCriticalSource.polynomial, ParameterSpatialSpecialization.equation, Fin.succ_inj] using H

theorem invalid (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) (hq : ¬ valid k b q) : value P read o k w b bits q = [] :=
  ite_eq_right hq

end LeanCanny.Encoding.BoundedCriticalSampleBlockCritical
