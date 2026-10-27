/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceSource
public import LeanCanny.Algebra.PrincipalParameterDegree

/-! # Native actual degrees and leading signs after algebraic specialization

The offset distinguishes a zero polynomial from a nonzero constant. Every
coefficient-zero test uses the original bivariate modular readers through
the ordered-root sign engine. No stability of the symbolic degree is assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

theorem coefficient_zero (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign P F (pair u (BinaryNatCode.encode k)) = [] ↔ (specialized P F u).coeff k = 0 := by
  rw [coefficientSign_packet]
  have he (s : SignType) : InfinitesimalSign.encode s = [] ↔ s = 0 := by cases s <;> decide
  rw [he, sign_eq_zero_iff]

noncomputable def offset (P : Readers) (F : Family) (u : List Bool) : ℕ :=
  if specialized P F u = 0 then 0 else (specialized P F u).natDegree + 1
noncomputable def degree (P : Readers) (F : Family) (u : List Bool) : ℕ := (specialized P F u).natDegree

theorem offset_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (offset P F u)) := by
  have hD : BinaryFn (fun u => F.degree (pairFst u)) := A.degree_binary.comp pairFst_mem_FP
  exact PolynomialDegreeBits.offsetEvaluator (coefficientSign_evaluator h A ha)
    (fun u => BinaryNatCode.encode (F.degree (pairFst u))) hD.bits_mem_FP (specialized P F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree P F u)
    (coefficient_zero P F)

theorem degree_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (degree P F u)) := by
  have hD : BinaryFn (fun u => F.degree (pairFst u)) := A.degree_binary.comp pairFst_mem_FP
  exact PolynomialDegreeBits.degreeEvaluator (coefficientSign_evaluator h A ha)
    (fun u => BinaryNatCode.encode (F.degree (pairFst u))) hD.bits_mem_FP (specialized P F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree P F u)
    (coefficient_zero P F)

theorem specialized_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    specialized P F (pair c (BinaryNatCode.encode r.val)) = F.slice c (BoundedProjectionOrderedRoot.root P c r).val := by
  have hr : pair c (BinaryNatCode.encode r.val) ∈ valid P := by
    simpa only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [specialized, ite_eq_left hr, pairFst_pair, point_packet]

theorem degree_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    degree P F (pair c (BinaryNatCode.encode r.val)) = (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).natDegree := by
  rw [degree, specialized_packet]

theorem offset_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    offset P F (pair c (BinaryNatCode.encode r.val)) =
      if F.slice c (BoundedProjectionOrderedRoot.root P c r).val = 0 then 0
      else (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).natDegree + 1 := by
  rw [offset, specialized_packet]

noncomputable def leading (P : Readers) (F : Family) (u : List Bool) : List Bool :=
  coefficientSign P F (pair u (BinaryNatCode.encode (degree P F u)))
theorem leading_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (leading P F) :=
  (degree_evaluator h A ha).withInput.chain (coefficientSign_evaluator h A ha)

theorem leading_packet (P : Readers) (F : Family) (u : List Bool) :
    leading P F u = InfinitesimalSign.encode (SignType.sign (specialized P F u).leadingCoeff) := by
  rw [leading, coefficientSign_packet, degree, Polynomial.coeff_natDegree]

noncomputable def nonzeroLanguage (P : Readers) (F : Family) : Language := {u | specialized P F u ≠ 0}
theorem nonzero_decider {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (nonzeroLanguage P F) := by
  apply (offset_evaluator h A ha).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [nonzeroLanguage, Set.mem_ofPred_eq, decide_eq_true_eq, BinaryNatCode.encode,
    ne_eq, BinaryNat.bits_eq_nil_iff, offset]
  split_ifs <;> simp_all

end LeanCanny.Encoding.BoundedAlgebraicSlice
