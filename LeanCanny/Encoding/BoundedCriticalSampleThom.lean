/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLabels
public import LeanCanny.Algebra.IteratedDerivativeSpace
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Algebra.SparseSignSpanning

/-! # Streamed Thom features of the actual critical-sample parameter

Derivative signs separate the filtered parameter roots. Sparse monomials in
these features span functions on the actual samples. The full signature is
an indexed mathematical function; native access reads one derivative
coefficient at a time with a binary derivative order.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleThom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  PrimitivePairBits.coefficient

noncomputable def polynomial (P : Readers) (c : List Bool) (k : ℕ) : Polynomial ℤ :=
  Polynomial.derivative^[k] (BoundedCriticalRationalCoordinates.parameter P c)

noncomputable def massExponent (P : Readers) (c : List Bool) : ℕ :=
  IteratedDerivativeBits.massBudget (BoundedCriticalRationalCoordinates.parameterDegree P c)
    (BoundedCriticalRationalCoordinates.baseHeight P c)

theorem massExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (massExponent P) :=
  IteratedDerivativeBits.massBudget_binary (BoundedCriticalRationalCoordinates.parameterDegree_binary h)
    (BoundedCriticalRationalCoordinates.baseHeight_binary h)

theorem degree (P : Readers) (c : List Bool) (k : ℕ) :
    (polynomial P c k).natDegree ≤ BoundedCriticalRationalCoordinates.parameterDegree P c :=
  (Polynomial.natDegree_iterate_derivative _ _).trans
    ((Nat.sub_le _ _).trans (BoundedCriticalRationalCoordinates.parameter_bounds P c).1)

theorem mass_bound (P : Readers) (c : List Bool) (k : ℕ) :
    coefficientMass (polynomial P c k) ≤ 2 ^ massExponent P c :=
  IteratedDerivativeBits.mass_bound _ _ _ (BoundedCriticalRationalCoordinates.parameter_bounds P c).1
    (fun i => (coeff_natAbs_le_coefficientMass _ i).trans
      (BoundedCriticalRationalCoordinates.parameter_bounds P c).2) k

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def order (q : List Bool) : List Bool := pairFst (pairSnd (pairFst q))
def index (q : List Bool) : List Bool := pairSnd (pairSnd (pairFst q))
def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem order_FP : order ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

def sourceQuery (t : List Bool) : List Bool :=
  pair (pair (original (pairFst t)) (pairSnd t)) (pairSnd (pairFst t))

theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

/-- Packet: `pair (pair context (pair derivativeOrder coefficientIndex)) modulusMinusOne`. -/
noncomputable def value (P : Readers) (q : List Bool) : List Bool :=
  residueBits (((polynomial P (original q) (Nat.fromBitsLE (order q))).coeff (Nat.fromBitsLE (index q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) := by
  have S := (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha).precompose sourceQuery sourceQuery_FP
  have hv : (fun q => Nat.fromBitsLE (modulus q)) = (fun q => Nat.fromBitsLE (pairSnd q) + 1) := by
    funext q
    simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  exact IteratedDerivativeBits.evaluatorWithModulus S index_FP order_FP modulus_FP
    (fun q => Nat.fromBitsLE (pairSnd q) + 1) hv (fun _ => by omega)
    (fun q => BoundedCriticalRationalCoordinates.parameter P (original q)) (by
      intro q i
      change PrimitivePairBits.coefficient (BoundedCriticalRationalCoordinates.parameter P)
        (sourceQuery (pair q (BinaryNatCode.encode i))) = _
      simp only [sourceQuery, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient,
        RationalSubstitution.IntegerBits.coefficientResidue]
      exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
        (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
          pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
        (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair]))

theorem value_packet (P : Readers) (c : List Bool) (k i : ℕ) (m : List Bool) :
    value P (pair (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode i))) m) =
      residueBits (((polynomial P c k).coeff i : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : pair (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode i))) m = z
  have hc : original z = c := by rw [original, ← hz, pairFst_pair, pairFst_pair]
  have hk : Nat.fromBitsLE (order z) = k := by
    rw [order, ← hz, pairFst_pair, pairSnd_pair, pairFst_pair]
    exact Nat.fromBitsLE_bits k
  have hi : Nat.fromBitsLE (index z) = i := by
    rw [index, ← hz, pairFst_pair, pairSnd_pair, pairSnd_pair]
    exact Nat.fromBitsLE_bits i
  have hm : pairSnd z = m := by rw [← hz, pairSnd_pair]
  subst c
  subst k
  subst i
  subst m
  rfl

abbrev Root (P : Readers) (c : List Bool) := {x // x ∈ BoundedCriticalSampleLabels.rootSet P c}
abbrev Feature (P : Readers) (c : List Bool) := Fin (BoundedCriticalRationalCoordinates.parameterDegree P c + 1)

noncomputable def signature (P : Readers) (c : List Bool) (x : Root P c) : Feature P c → SignType :=
  ThomEncoding.signature ((BoundedCriticalRationalCoordinates.parameter P c).map (Int.castRingHom ℝ))
    (BoundedCriticalRationalCoordinates.parameterDegree P c) x.val

theorem signature_injective (P : Readers) (c : List Bool) : Function.Injective (signature P c) := by
  intro a b he
  apply Subtype.ext
  apply ThomEncoding.root_eq ((BoundedCriticalRationalCoordinates.parameter P c).map (Int.castRingHom ℝ))
    (BoundedCriticalSampleLabels.mapped_ne_zero P c) (BoundedCriticalRationalCoordinates.parameterDegree P c)
    (Polynomial.natDegree_map_le.trans (BoundedCriticalRationalCoordinates.parameter_bounds P c).1)
  · rw [Polynomial.eval_map]
    exact ((BoundedCriticalSampleLabels.mem_rootSet P c a.val).mp a.property).1
  · rw [Polynomial.eval_map]
    exact ((BoundedCriticalSampleLabels.mem_rootSet P c b.val).mp b.property).1
  · intro k hk
    exact congrFun he ⟨k, by omega⟩

noncomputable def vector (P : Readers) (c : List Bool) (d : Feature P c →₀ ℕ) : Root P c → ℚ :=
  MonomialEvaluationBasis.vector (MvPolynomial.aeval (R := ℚ) (fun i x => (signature P c x i : ℚ))) d

theorem sparse_span (P : Readers) (c : List Bool) :
    Submodule.span ℚ (vector P c '' {d | d.support.card ≤ BoundedFullCriticalSamples.labelWidth P c ∧
      ∀ i, d i ≤ 2}) = ⊤ := by
  apply SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Feature P c))
    (signature P c) (signature_injective P c) (BoundedFullCriticalSamples.labelWidth P c)
  rw [Fintype.card_coe, BoundedCriticalSampleLabels.rootSet_card]
  exact (BoundedFullCriticalSamples.finite_samples P c).2

end LeanCanny.Encoding.BoundedCriticalSampleThom
