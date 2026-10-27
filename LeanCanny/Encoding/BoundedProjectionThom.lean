/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootCount
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Algebra.IteratedDerivativeSpace

/-! # Streamed derivative features for symbolic projection-root labels

The full derivative-sign signature uniquely identifies every actual sample.
It is an indexed function, not a polynomial-sized output word. Native modular
access and uniform binary bounds prepare its features for sign determination;
`BoundedProjectionSignatureRead` enumerates the distinct signatures using short
root ordinals and reads their individual derivative signs in native space.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionThom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial

noncomputable def polynomial (P : Readers) (c : List Bool) (k : ℕ) : Polynomial ℤ :=
  Polynomial.derivative^[k] (BoundedCriticalProjection.polynomial P c)

noncomputable def massExponent (P : Readers) (c : List Bool) : ℕ :=
  IteratedDerivativeBits.massBudget (BoundedProjectionRootCount.degree P c) (BoundedCriticalProjection.coefficientBits P c)

theorem massExponent_binary {P : Readers} (h : P.PolyTime) : BinaryFn (massExponent P) :=
  IteratedDerivativeBits.massBudget_binary (BoundedProjectionRootCount.degree_binary h)
    (BoundedCriticalProjection.coefficientBits_binary h)

theorem degree (P : Readers) (c : List Bool) (k : ℕ) :
    (polynomial P c k).natDegree ≤ BoundedProjectionRootCount.degree P c :=
  (Polynomial.natDegree_iterate_derivative _ _).trans
    ((Nat.sub_le _ _).trans (BoundedCriticalProjection.polynomial_degree P c))

theorem mass_bound (P : Readers) (c : List Bool) (k : ℕ) :
    coefficientMass (polynomial P c k) ≤ 2 ^ massExponent P c :=
  IteratedDerivativeBits.mass_bound _ _ _ (BoundedCriticalProjection.polynomial_degree P c)
    (fun i => (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
      (BoundedCriticalProjection.polynomial_coefficient_bits P c i))) k

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def order (q : List Bool) : List Bool := pairFst (pairSnd (pairFst q))
def index (q : List Bool) : List Bool := pairSnd (pairSnd (pairFst q))
def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem order_FP : order ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

def sourceQuery (t : List Bool) : List Bool :=
  pair (pair (original (pairFst t)) (pairSnd (pairFst t))) (pairSnd t)

theorem sourceQuery_FP : sourceQuery ∈ FP := by
  have h := mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP original_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [sourceQuery, Function.comp_apply])

/-- Packet: `pair (pair context (pair derivativeOrder coefficientIndex)) modulusMinusOne`. -/
noncomputable def value (P : Readers) (q : List Bool) : List Bool :=
  residueBits (((polynomial P (original q) (Nat.fromBitsLE (order q))).coeff (Nat.fromBitsLE (index q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) := by
  have S := (BoundedProjectionCoefficient.evaluator h ha).precompose sourceQuery sourceQuery_FP
  have hv : (fun q => Nat.fromBitsLE (modulus q)) = (fun q => Nat.fromBitsLE (pairSnd q) + 1) := by
    funext q
    simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  exact IteratedDerivativeBits.evaluatorWithModulus S index_FP order_FP modulus_FP
    (fun q => Nat.fromBitsLE (pairSnd q) + 1) hv (fun _ => by omega)
    (fun q => BoundedCriticalProjection.polynomial P (original q))
    (by
      intro q i
      change BoundedProjectionCoefficient.value P (sourceQuery (pair q (BinaryNatCode.encode i))) = _
      simp only [sourceQuery, pairFst_pair, pairSnd_pair]
      exact BoundedProjectionCoefficient.value_packet P (original q) (pairSnd q) i)

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

noncomputable def signature (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    Fin (BoundedProjectionRootCount.degree P c + 1) → SignType :=
  ThomEncoding.signature ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ))
    (BoundedProjectionRootCount.degree P c)
    (BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val)

theorem signature_apply (P : Readers) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (k : Fin (BoundedProjectionRootCount.degree P c + 1)) :
    signature P c x k = SignType.sign ((polynomial P c k.val).eval₂ (Int.castRingHom ℝ)
      (BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val)) := by
  simp only [signature, ThomEncoding.signature, ThomEncoding.sign, polynomial,
    Polynomial.iterate_derivative_map, Polynomial.eval_map]

theorem signature_injective (P : Readers) (c : List Bool) : Function.Injective (signature P c) := by
  intro a b he
  apply BoundedCriticalSeparator.value_injective P c
  apply ThomEncoding.root_eq ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ))
    (BoundedCriticalLabels.mapped_ne_zero P c) (BoundedProjectionRootCount.degree P c)
    (Polynomial.natDegree_map_le.trans (BoundedCriticalProjection.polynomial_degree P c))
  · rw [Polynomial.eval_map]
    exact BoundedCriticalProjection.polynomial_eval_sample P c a
  · rw [Polynomial.eval_map]
    exact BoundedCriticalProjection.polynomial_eval_sample P c b
  · intro k hk
    exact congrFun he ⟨k, by omega⟩

theorem signature_eq_iff_label_eq (P : Readers) (c : List Bool) (a b : BoundedFullCriticalSamples.Samples P c) :
    signature P c a = signature P c b ↔ BoundedCriticalLabels.label P c a = BoundedCriticalLabels.label P c b := by
  rw [(signature_injective P c).eq_iff, (BoundedCriticalLabels.label_injective P c).eq_iff]

end LeanCanny.Encoding.BoundedProjectionThom
