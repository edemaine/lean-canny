/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceSource

/-! # Native actual degrees in slices based at actual samples -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSlice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open scoped Classical

theorem coefficient_zero (P : Readers) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign P F (pair u (BinaryNatCode.encode k)) = [] ↔ (specialized P F u).coeff k = 0 := by
  rw [coefficientSign_packet]
  have he (s : SignType) : InfinitesimalSign.encode s = [] ↔ s = 0 := by cases s <;> decide
  rw [he, sign_eq_zero_iff]

noncomputable def degree (P : Readers) (F : Family) (u : List Bool) : ℕ := (specialized P F u).natDegree
noncomputable def offset (P : Readers) (F : Family) (u : List Bool) : ℕ :=
  if specialized P F u = 0 then 0 else degree P F u + 1

theorem degree_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (degree P F u)) := by
  have hd : BinaryFn (fun u => F.degree (context u)) := A.degree_binary.comp context_FP
  exact PolynomialDegreeBits.degreeEvaluator (coefficientSign_evaluator h A ha)
    (fun u => BinaryNatCode.encode (F.degree (context u))) hd.bits_mem_FP (specialized P F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree P F u)
    (coefficient_zero P F)

theorem offset_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (offset P F u)) := by
  have hd : BinaryFn (fun u => F.degree (context u)) := A.degree_binary.comp context_FP
  exact PolynomialDegreeBits.offsetEvaluator (coefficientSign_evaluator h A ha)
    (fun u => BinaryNatCode.encode (F.degree (context u))) hd.bits_mem_FP (specialized P F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree P F u)
    (coefficient_zero P F)

noncomputable def leading (P : Readers) (F : Family) (u : List Bool) : List Bool :=
  coefficientSign P F (pair u (BinaryNatCode.encode (degree P F u)))
theorem leading_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (leading P F) :=
  (degree_evaluator h A ha).withInput.chain (coefficientSign_evaluator h A ha)
theorem leading_packet (P : Readers) (F : Family) (u : List Bool) :
    leading P F u = InfinitesimalSign.encode (SignType.sign (specialized P F u).leadingCoeff) := by
  rw [leading, coefficientSign_packet, degree, Polynomial.coeff_natDegree]

theorem degree_valid (P : Readers) (F : Family) (u : List Bool) (hu : 0 < degree P F u) : u ∈ valid P := by
  by_contra hv
  have hz : degree P F u = 0 := by rw [degree, specialized, ite_eq_right hv, natDegree_zero]
  omega

end LeanCanny.Encoding.BoundedCriticalSampleSlice
