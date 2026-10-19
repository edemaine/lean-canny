/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeCoefficientSpace
public import LeanCanny.Algebra.PolynomialProductSpace

/-! # Certified coefficients of the actual derivative query product

Original head and query coefficient routines supply both factors. The
derivative's coefficient multiplier and the two-factor product are evaluated
internally. The coefficient index is binary, including on noncanonical inputs.
-/

@[expose] public section

namespace LeanCanny.Algebra.DerivativeProductBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

structure Family where
  modulus : List Bool → ℕ
  head : (c : List Bool) → (ZMod (modulus c))[X]
  query : (c : List Bool) → (ZMod (modulus c))[X]
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.coefficientValue (F : Family) (c : List Bool) (k : ℕ) : List Bool :=
  residueBits ((F.query c * (F.head c).derivative).coeff k)

noncomputable def Family.value (F : Family) (q : List Bool) : List Bool :=
  F.coefficientValue (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem Family.value_packet (F : Family) (c : List Bool) (k : ℕ) :
    F.value (pair c (BinaryNatCode.encode k)) = residueBits ((F.query c * (F.head c).derivative).coeff k) := by
  simp only [Family.value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def Family.product (F : Family) : PolynomialProduct.ModularFamily where
  count _ := 2
  modulus q := F.modulus (pairFst q)
  degree q := Nat.fromBitsLE (pairSnd q)
  factor q i := if i = 0 then F.query (pairFst q) else (F.head (pairFst q)).derivative
  modulus_ne_zero q := F.modulus_ne_zero (pairFst q)

set_option backward.isDefEq.respectTransparency false in
theorem Family.product_value (F : Family) (q : List Bool) : F.product.value q = F.value q := by
  have hprod : (∏ i ∈ Finset.range 2,
      if i = 0 then F.query (pairFst q) else (F.head (pairFst q)).derivative) =
      F.query (pairFst q) * (F.head (pairFst q)).derivative := by
    change (∏ i ∈ Finset.range (1 + 1), _) = _
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    simp
  simpa only [PolynomialProduct.ModularFamily.value, Family.product, Family.value, Family.coefficientValue] using
    congrArg (fun p => residueBits (p.coeff (Nat.fromBitsLE (pairSnd q)))) hprod

structure Access (F : Family) where
  modulus : List Bool → List Bool
  headCoefficient : List Bool → List Bool
  queryCoefficient : List Bool → List Bool
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  head_eq : ∀ c k, headCoefficient (pair c (BinaryNatCode.encode k)) = residueBits ((F.head c).coeff k)
  query_eq : ∀ c k, queryCoefficient (pair c (BinaryNatCode.encode k)) = residueBits ((F.query c).coeff k)

def factorIndex (r : List Bool) : List Bool := pairFst (pairSnd r)
def sourceQuery (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd (pairSnd r))
def factorValue {F : Family} (a : Access F) (r : List Bool) : List Bool :=
  if Nat.fromBitsLE (factorIndex r) = 0 then a.queryCoefficient (sourceQuery r)
  else DerivativeBits.value a.modulus a.headCoefficient (sourceQuery r)

theorem factorIndex_mem_FP : factorIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def factorEvaluator {F : Family} (a : Access F) (hm : a.modulus ∈ FP)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction (factorValue a) := by
  let D := DerivativeBits.evaluator P a.modulus hm
  have hz : FPPred (fun r => Nat.fromBitsLE (factorIndex r) = 0) :=
    (BinaryNat.lt_fppred factorIndex_mem_FP (constFn_mem_FP [true])).of_iff
    (fun r => by change Nat.fromBitsLE (factorIndex r) < 1 ↔ Nat.fromBitsLE (factorIndex r) = 0; omega)
  let E := SpaceFunction.branch (fun r => decide (Nat.fromBitsLE (factorIndex r) = 0))
    hz.flag_mem_FP (Q.precompose sourceQuery sourceQuery_mem_FP) (D.precompose sourceQuery sourceQuery_mem_FP)
  refine E.congr (funext fun r => ?_)
  simp only [factorValue, Function.comp_apply, decide_eq_true_eq]

noncomputable def Access.product {F : Family} (a : Access F) : PolynomialProduct.ModularAccess F.product where
  count _ := [false, true]
  modulus := a.modulus ∘ pairFst
  degree := BinaryNat.normalize ∘ pairSnd
  coefficient := factorValue a
  count_eq _ := by simp only [Family.product]; rfl
  modulus_eq q := a.modulus_eq (pairFst q)
  degree_eq q := BinaryNat.normalize_eq_bits (pairSnd q)
  coefficient_eq q i _ k := by
    simp only [factorValue, factorIndex, sourceQuery, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Family.product]
    by_cases hi : i = 0
    · simp only [ite_eq_left hi]
      exact a.query_eq (pairFst q) k
    · simp only [ite_eq_right hi]
      exact DerivativeBits.packet a.modulus a.headCoefficient (pairFst q) (F.modulus (pairFst q))
        (F.head (pairFst q)) (a.modulus_eq _) (a.head_eq _) k

noncomputable def Access.evaluator {F : Family} (a : Access F) (hm : a.modulus ∈ FP)
    (P : SpaceFunction a.headCoefficient) (Q : SpaceFunction a.queryCoefficient) :
    SpaceFunction F.value := by
  have hm' := mem_FP_comp pairFst_mem_FP hm
  have hd' := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hc : a.product.ControlsPolyTime := by
    constructor
    · simpa only [Access.product] using constFn_mem_FP ([false, true] : List Bool)
    · simpa only [Access.product] using hm'
    · simpa only [Access.product] using hd'
  let E := PolynomialProduct.ModularAccess.evaluator a.product hc (factorEvaluator a hm P Q)
  exact E.congr (funext F.product_value)

end LeanCanny.Algebra.DerivativeProductBits
