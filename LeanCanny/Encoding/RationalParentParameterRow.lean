/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentJointSource

/-! # Native coefficients of the retained parent equation

Only variable zero may occur in this row. A native spatial-exponent mask
rejects every other monomial before querying the native parameter reader.
The common joint-system exponent width is used on every raw query.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentParameterRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open RationalParentJointSource (Inputs)
open scoped Classical
attribute [local irreducible] RationalParentJointSource.width

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def target (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def spatialTarget (F : Inputs) (q : List Bool) : List Bool :=
  (target q).drop (RationalParentJointSource.width F (origin q))

theorem spatialTarget_FP {F : Inputs} (h : F.Access) : spatialTarget F ∈ FP :=
  drop_mem_FP target_FP ((RationalParentJointSource.width_unary h).comp origin_FP)

noncomputable def spatialZero (F : Inputs) : List Bool → Prop :=
  FixedWidthQuery.Bounded (fun q => F.block.dim (origin q))
    (fun q => RationalParentJointSource.width F (origin q)) (spatialTarget F) (fun _ => 0)
noncomputable instance (F : Inputs) (q : List Bool) :
    Decidable (spatialZero F q) := Classical.propDecidable _

theorem spatialZero_pred {F : Inputs} (h : F.Access) : FPPred (spatialZero F) :=
  FixedWidthQuery.bounded_fppred (h.block.dim.comp origin_FP)
    ((RationalParentJointSource.width_unary h).comp origin_FP) (UnaryFn.const 0) (spatialTarget_FP h)

theorem spatialZero_packet (F : Inputs) (u : List Bool) (r m : ℕ) :
    spatialZero F (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) ↔
      ∀ i : Fin (F.block.dim u), nativeExponent (Equiv.refl (Fin (F.block.dim u + 1))) (RationalParentJointSource.width F u) r i.succ = 0 := by
  have he (i : ℕ) :
      FixedWidthQuery.coordinate (fun q => RationalParentJointSource.width F (origin q))
        (spatialTarget F) (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) i =
          entry (RationalParentJointSource.width F u) r (i + 1) := by
    simp only [FixedWidthQuery.coordinate, spatialTarget, target, origin, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, List.drop_drop, entry]
    congr 3
    ring
  simp only [spatialZero, FixedWidthQuery.Bounded, he]
  simp only [origin, pairFst_pair, Nat.le_zero,
    nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply, Fin.val_succ, Fin.forall_iff]

noncomputable def query (F : Inputs) (q : List Bool) : List Bool :=
  pair (pair (origin q) (BinaryNat.normalize ((target q).take
    (RationalParentJointSource.width F (origin q))))) (BinaryNat.normalize (pairSnd q))

theorem query_FP {F : Inputs} (h : F.Access) : query F ∈ FP :=
  mem_FP_pair (mem_FP_pair origin_FP
    (mem_FP_comp (take_mem_FP target_FP ((RationalParentJointSource.width_unary h).comp origin_FP))
      BinaryNat.normalize_mem_FP)) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def value (F : Inputs) (q : List Bool) : List Bool :=
  if spatialZero F q then PrimitivePairBits.coefficient (F.parent.polynomial) (query F q) else []

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) := by
  exact (SpaceFunction.branch (fun q => decide (spatialZero F q)) (spatialZero_pred h).flag_mem_FP
    (h.parent.coefficient.precompose (query F) (query_FP h))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem packet (F : Inputs) (u : List Bool) (r m : ℕ) :
    value F (pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)) =
      MatrixPower.residueBits (((IndexedMultivariateRational.parameter (F.block.dim u)
        (F.parent.polynomial u)).coeff
          (nativeExponent (Equiv.refl (Fin (F.block.dim u + 1))) (RationalParentJointSource.width F u) r) : ℤ) : ZMod (m + 1)) := by
  let q := pair (pair u (BinaryNatCode.encode r)) (BinaryNatCode.encode m)
  have hp : PrimitivePairBits.coefficient (F.parent.polynomial) (query F q) =
      MatrixPower.residueBits (((F.parent.polynomial u).coeff
        (entry (RationalParentJointSource.width F u) r 0) : ℤ) : ZMod (m + 1)) := by
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      query, q, origin, target, pairFst_pair, pairSnd_pair,
      BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, entry, Nat.zero_mul, List.drop_zero]
    rfl
  rw [RetainedParameterPolynomial.coefficient]
  by_cases hz : spatialZero F q
  · rw [value, ite_eq_left hz, ite_eq_left ((spatialZero_packet F u r m).mp hz), hp]
    rfl
  · rw [value, ite_eq_right hz, ite_eq_right (fun h => hz ((spatialZero_packet F u r m).mpr h))]
    simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
    rfl

end LeanCanny.Encoding.RationalParentParameterRow
