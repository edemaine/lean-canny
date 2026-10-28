/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleJointSource

/-! # Native coefficients of the retained parent equation

Only variable zero may occur in this row. A native spatial-exponent mask
rejects every other monomial before querying the original parameter reader.
The common joint-system exponent width is used on every raw query.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleParameterRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter BoundedCriticalSampleJointSource.width

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def target (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def spatialTarget (P : Readers) (read : List Bool → List Bool) (q : List Bool) : List Bool :=
  (target q).drop (BoundedCriticalSampleJointSource.width P read (origin q))

theorem spatialTarget_FP {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    spatialTarget P read ∈ FP :=
  drop_mem_FP target_FP ((BoundedCriticalSampleJointSource.width_unary h read hr).comp origin_FP)

noncomputable def spatialZero (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) : List Bool → Prop :=
  FixedWidthQuery.Bounded (fun q => k (origin q))
    (fun q => BoundedCriticalSampleJointSource.width P read (origin q)) (spatialTarget P read) (fun _ => 0)
noncomputable instance (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (q : List Bool) :
    Decidable (spatialZero P read k q) := Classical.propDecidable _

theorem spatialZero_pred {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) : FPPred (spatialZero P read k) :=
  FixedWidthQuery.bounded_fppred (hk.comp origin_FP)
    ((BoundedCriticalSampleJointSource.width_unary h read hr).comp origin_FP) (UnaryFn.const 0) (spatialTarget_FP h read hr)

theorem spatialZero_packet (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) (r m : ℕ) :
    spatialZero P read k (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) ↔
      ∀ i : Fin (k u), nativeExponent (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleJointSource.width P read u) r i.succ = 0 := by
  have he (i : ℕ) :
      FixedWidthQuery.coordinate (fun q => BoundedCriticalSampleJointSource.width P read (origin q))
        (spatialTarget P read) (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) i =
          entry (BoundedCriticalSampleJointSource.width P read u) r (i + 1) := by
    simp only [FixedWidthQuery.coordinate, spatialTarget, target, origin, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, List.drop_drop, entry]
    congr 3
    ring
  simp only [spatialZero, FixedWidthQuery.Bounded, he]
  simp only [origin, pairFst_pair, Nat.le_zero,
    nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply, Fin.val_succ, Fin.forall_iff]

noncomputable def query (P : Readers) (read : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (pairFst (origin q)) (BinaryNat.normalize ((target q).take
    (BoundedCriticalSampleJointSource.width P read (origin q))))) (BinaryNat.normalize (pairSnd q))

theorem query_FP {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) : query P read ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp origin_FP pairFst_mem_FP)
    (mem_FP_comp (take_mem_FP target_FP ((BoundedCriticalSampleJointSource.width_unary h read hr).comp origin_FP))
      BinaryNat.normalize_mem_FP)) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def value (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (q : List Bool) : List Bool :=
  if spatialZero P read k q then PrimitivePairBits.coefficient (BoundedCriticalRationalCoordinates.parameter P) (query P read q) else []

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {k : List Bool → ℕ} (hk : UnaryFn k) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P read k) := by
  exact (SpaceFunction.branch (fun q => decide (spatialZero P read k q)) (spatialZero_pred h read hr hk).flag_mem_FP
    ((BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha).precompose (query P read) (query_FP h read hr))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem packet (P : Readers) (read : List Bool → List Bool) (k : List Bool → ℕ) (u : List Bool) (r m : ℕ) :
    value P read k (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) =
      MatrixPower.residueBits (((IndexedMultivariateRational.parameter (k u)
        (BoundedCriticalRationalCoordinates.parameter P (pairFst u))).coeff
          (nativeExponent (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleJointSource.width P read u) r) : ℤ) : ZMod (m + 1)) := by
  let q := pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)
  have hp : PrimitivePairBits.coefficient (BoundedCriticalRationalCoordinates.parameter P) (query P read q) =
      MatrixPower.residueBits (((BoundedCriticalRationalCoordinates.parameter P (pairFst u)).coeff
        (entry (BoundedCriticalSampleJointSource.width P read u) r 0) : ℤ) : ZMod (m + 1)) := by
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      query, q, origin, target, pairFst_pair, pairSnd_pair,
      BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, entry, Nat.zero_mul, List.drop_zero]
    rfl
  rw [RetainedParameterPolynomial.coefficient]
  by_cases hz : spatialZero P read k q
  · rw [value, ite_eq_left hz, ite_eq_left ((spatialZero_packet P read k u r m).mp hz), hp]
    rfl
  · rw [value, ite_eq_right hz, ite_eq_right (fun h => hz ((spatialZero_packet P read k u r m).mpr h))]
    simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
    rfl

end LeanCanny.Encoding.BoundedCriticalSampleParameterRow
