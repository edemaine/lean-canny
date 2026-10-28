/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentFullBlockCoefficient
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCritical
public import LeanCanny.Encoding.FixedWidthQuerySpace
public import LeanCanny.Algebra.FixedWidthCriticalDirectionSpace
public import LeanCanny.Encoding.RationalParentFullBlockCriticalSource

/-! # Native critical-equation coefficients over full-source sample blocks

A request is `pair (pair sourceRecord (pair row monomial)) modulusMinusOne`.
The row and pivot name free block coordinates; variable zero stays the sample
parameter. Native derivative calls and modular arithmetic construct each
critical equation directly from the collected full-source coefficients. The
direction record may be computed in polynomial space. Invalid
rows or pivots return zero, including empty spatial blocks.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentFullBlockCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FixedWidthPolynomial RationalParentFullBlock BoundedCriticalSampleBlockCritical
open scoped Classical
attribute [local irreducible] RationalParentFullBlockPolynomial.polynomial
  RationalParentFullBlockCoefficient.value FixedWidthCriticalBits.value width degreeBound
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Inputs) : List Bool → List Bool :=
  RationalParentFullBlockCoefficient.value F ∘ sourceQuery

theorem source_evaluator {F : Inputs} (h : F.Access)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (source F) :=
  (RationalParentFullBlockCoefficient.evaluator h htS).precompose sourceQuery sourceQuery_FP

theorem source_packet (F : Inputs) (q : List Bool) (s : ℕ) :
    source F (pair q (BinaryNatCode.encode s)) = MatrixPower.residueBits
      (((RationalParentFullBlockPolynomial.polynomial F (origin q)).coeff
        (nativeExponent (Equiv.refl (Fin (F.dim (origin q) + 1))) (width F (origin q)) s) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have H := RationalParentFullBlockCoefficient.packet F (origin q) s
    (Nat.fromBitsLE (pairSnd q) + 1) (by omega)
  simpa only [source, Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.add_sub_cancel] using H

theorem direction_evaluator {k w : List Bool → ℕ} (hk : UnaryFn k) (hw : UnaryFn w)
    {bits : List Bool → List Bool} (E : SpaceFunction bits) : SpaceFunction (direction k w bits) :=
  (FixedWidthQuery.read_evaluator hk hw E).precompose directionQuery directionQuery_FP

noncomputable def raw (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthCriticalBits.value (fun q => F.dim (origin q) + 1) (fun q => width F (origin q))
    (fun q => degreeBound F (origin q)) (base F.dim b) (selected F.dim) target modulus (direction F.dim w bits) (source F)

theorem raw_evaluator {F : Inputs} (h : F.Access)
    {w b : List Bool → ℕ} (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (E : SpaceFunction bits)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (raw F w b bits) :=
  FixedWidthCriticalBits.evaluator_space _ _ _ _ _ _ _ _ (source_evaluator h htS)
    ((h.dim.comp origin_FP).add (UnaryFn.const 1)) ((width_unary h).comp origin_FP)
    ((degreeBound_binary h).comp origin_FP) (base_unary h.dim hb) (selected_unary h.dim)
    target_FP modulus_FP (direction_evaluator h.dim hw E)

noncomputable def value (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) : List Bool :=
  if valid F.dim b q then raw F w b bits q else []

theorem evaluator {F : Inputs} (h : F.Access)
    {w b : List Bool → ℕ} (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (E : SpaceFunction bits)
    (htS : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u) : SpaceFunction (value F w b bits) := by
  exact (SpaceFunction.branch (fun q => decide (valid F.dim b q)) (valid_pred h.dim hb).flag_mem_FP
    (raw_evaluator h hw hb E htS) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq])

theorem packet (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot i : Fin (F.dim u)) (hb : b u = pivot.val) (r m : ℕ) :
    value F w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
        MatrixPower.residueBits (((RationalParentFullBlockCriticalSource.polynomial F w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (F.dim u + 1))) (width F u) r) : ℤ) : ZMod (m + 1)) := by
  let q := pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)
  have hq : origin q = u := by simp only [q, origin, pairFst_pair]
  have hr : Nat.fromBitsLE (row q) = i.val := by
    simp only [q, row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have ht : Nat.fromBitsLE (target q) = r := by
    simp only [q, target, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hm : Nat.fromBitsLE (pairSnd q) = m := by
    simp only [q, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hdirection : direction F.dim w bits q =
      BinaryNatCode.encode (RationalParentFullBlockCriticalSource.direction F.dim w bits u i) := by
    have hrow : BinaryNat.normalize (row q) = BinaryNatCode.encode i.val := by
      simp only [BinaryNat.normalize_eq_bits, hr, BinaryNatCode.encode]
    rw [direction, Function.comp_apply, directionQuery, hq, hrow]
    exact FixedWidthQuery.read_packet F.dim w bits u i.val
  have hv : valid F.dim b q := by
    change b (origin q) < F.dim (origin q) ∧ Nat.fromBitsLE (row q) < F.dim (origin q)
    rw [hq, hr, hb]
    exact ⟨pivot.isLt, i.isLt⟩
  have H := FixedWidthCriticalBits.packet (fun z => F.dim (origin z) + 1) (fun z => width F (origin z))
    (fun z => degreeBound F (origin z)) (base F.dim b) (selected F.dim) target modulus (direction F.dim w bits)
    (Equiv.refl (Fin (F.dim u + 1))) (RationalParentFullBlockPolynomial.polynomial F u) pivot.succ i.succ
    (RationalParentFullBlockCriticalSource.direction F.dim w bits u i) m (source F) q
    (by rw [hq]) (by simp only [base, hq, hb, Nat.min_eq_left pivot.isLt.le]; rfl)
    (by simp only [selected, hr, hq, Nat.min_eq_left i.isLt.le]; rfl)
    (by rw [hq]; exact degreeBound_pos F u) (by rw [hq]; exact RationalParentFullBlockCriticalSource.source_degree F u)
    (by rw [hq]; exact degree_lt F u)
    (by simp only [modulus, BinaryNat.succ_eq_bits, hm, BinaryNatCode.encode]) hdirection
    (by
      intro s
      have hs := source_packet F q s
      have hc := congrArg (fun v => (RationalParentFullBlockPolynomial.polynomial F v).coeff
        (nativeExponent (Equiv.refl (Fin (F.dim v + 1))) (width F v) s)) hq
      rw [hc, hm] at hs
      simpa only [hq] using hs)
  change (if valid F.dim b q then raw F w b bits q else []) = _
  rw [ite_eq_left hv]
  simpa only [raw, hq, ht,
    RationalParentFullBlockCriticalSource.polynomial, ParameterSpatialSpecialization.equation, Fin.succ_inj] using H

theorem invalid (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) (hq : ¬ valid F.dim b q) : value F w b bits q = [] :=
  ite_eq_right hq

end LeanCanny.Encoding.RationalParentFullBlockCritical
