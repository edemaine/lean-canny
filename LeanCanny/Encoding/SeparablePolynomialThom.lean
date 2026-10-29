/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparablePolynomialFamily
public import LeanCanny.Algebra.IteratedDerivativeSpace
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Algebra.SparseSignSpanning

/-! # Native derivative-sign probes for separable parent equations

The degree and mass controls and coefficient reader come from the parameter
family. Every binary derivative order has native coefficient access. The
complete derivative-sign signature identifies each real parent root.
-/

@[expose] public section
namespace LeanCanny.Encoding.SeparablePolynomialThom
open LeanCanny.Algebra LeanCanny.Computation
open SeparablePolynomialFamily (Source Access)
open Brackets MatrixPower
open scoped Classical
attribute [local irreducible] PrimitivePairBits.coefficient

theorem mapped_ne_zero (P : Source) (c : List Bool) :
    (P.polynomial c).map (Int.castRingHom ℝ) ≠ 0 :=
  (SeparablePolynomialFamily.separable_in_field P c).ne_zero

noncomputable def polynomial (P : Source) (c : List Bool) (k : ℕ) : Polynomial ℤ :=
  Polynomial.derivative^[k] (P.polynomial c)

noncomputable def massExponent (P : Source) (c : List Bool) : ℕ :=
  IteratedDerivativeBits.massBudget (P.degree c)
    (P.mass c)

theorem massExponent_binary {P : Source} (h : Access P) : BinaryFn (massExponent P) :=
  IteratedDerivativeBits.massBudget_binary h.degree
    h.mass

theorem degree (P : Source) (c : List Bool) (k : ℕ) :
    (polynomial P c k).natDegree ≤ P.degree c :=
  (Polynomial.natDegree_iterate_derivative _ _).trans
    ((Nat.sub_le _ _).trans (P.degree_le c))

theorem mass_bound (P : Source) (c : List Bool) (k : ℕ) :
    coefficientMass (polynomial P c k) ≤ 2 ^ massExponent P c :=
  IteratedDerivativeBits.mass_bound _ _ _ (P.degree_le c)
    (fun i => (coeff_natAbs_le_coefficientMass _ i).trans
      (P.mass_le c)) k

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
noncomputable def value (P : Source) (q : List Bool) : List Bool :=
  residueBits (((polynomial P (original q) (Nat.fromBitsLE (order q))).coeff (Nat.fromBitsLE (index q)) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem evaluator {P : Source} (h : Access P) : SpaceFunction (value P) := by
  have S := h.coefficient.precompose sourceQuery sourceQuery_FP
  have hv : (fun q => Nat.fromBitsLE (modulus q)) = (fun q => Nat.fromBitsLE (pairSnd q) + 1) := by
    funext q
    simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  exact IteratedDerivativeBits.evaluatorWithModulus S index_FP order_FP modulus_FP
    (fun q => Nat.fromBitsLE (pairSnd q) + 1) hv (fun _ => by omega)
    (fun q => P.polynomial (original q)) (by
      intro q i
      change PrimitivePairBits.coefficient (P.polynomial)
        (sourceQuery (pair q (BinaryNatCode.encode i))) = _
      simp only [sourceQuery, pairFst_pair, pairSnd_pair, PrimitivePairBits.coefficient,
        RationalSubstitution.IntegerBits.coefficientResidue]
      exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
        (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
          pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
        (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair]))

theorem value_packet (P : Source) (c : List Bool) (k i : ℕ) (m : List Bool) :
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

theorem root_eq_iff (P : Source) (u : List Bool) (a b : ℝ)
    (ha : (P.polynomial u).eval₂ (Int.castRingHom ℝ) a = 0)
    (hb : (P.polynomial u).eval₂ (Int.castRingHom ℝ) b = 0) :
    a = b ↔ ∀ k ≤ P.degree u,
      SignType.sign ((polynomial P u k).eval₂ (Int.castRingHom ℝ) a) =
        SignType.sign ((polynomial P u k).eval₂ (Int.castRingHom ℝ) b) := by
  constructor
  · intro h k _
    rw [h]
  · intro hs
    apply ThomEncoding.root_eq ((P.polynomial u).map (Int.castRingHom ℝ)) (mapped_ne_zero P u)
      (P.degree u) (Polynomial.natDegree_map_le.trans (P.degree_le u))
    · simpa only [Polynomial.eval_map] using ha
    · simpa only [Polynomial.eval_map] using hb
    · intro k hk
      simpa only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map, polynomial] using hs k hk

end LeanCanny.Encoding.SeparablePolynomialThom
