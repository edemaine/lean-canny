/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateQueryProductBounds
public import LeanCanny.Algebra.SignQueryProductSpace

/-! # Native coefficients of indexed bivariate product queries

Kronecker substitution uses a radix valid for the entire product. Original
factor queries divide a univariate index into the two independent indices.
The existing streamed product algorithm then computes one coefficient. Inner
indices outside the product's radix are rejected before the product call.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateQueryProductBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def modulus (z : List Bool) : List Bool := pairSnd (pairFst z)
def innerWord (z : List Bool) : List Bool := pairFst (pairSnd z)
def outerWord (z : List Bool) : List Bool := pairSnd (pairSnd z)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem innerWord_FP : innerWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem outerWord_FP : outerWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

noncomputable def factorQuery (F : Family) (r : List Bool) : List Bool :=
  pair (pair (pair (origin (pairFst r)) (pairFst (pairSnd r))) (modulus (pairFst r)))
    (pair (BinaryNat.mod (pair (pairSnd (pairSnd r)) (BinaryNatCode.encode (F.radix (origin (pairFst r))))))
      (BinaryNat.div (pair (pairSnd (pairSnd r)) (BinaryNatCode.encode (F.radix (origin (pairFst r)))))))

theorem factorQuery_FP {F : Family} (A : Access F) : factorQuery F ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP origin_FP
  have hr := mem_FP_comp hc (radix_binary A).bits_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hk := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP modulus_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair hc hi) hm)
    (mem_FP_pair (mem_FP_comp (mem_FP_pair hk hr) BinaryNat.mod_mem_FP)
      (mem_FP_comp (mem_FP_pair hk hr) BinaryNat.div_mem_FP))

noncomputable def factor {F : Family} (A : Access F) : List Bool → List Bool := A.reader.coefficient ∘ factorQuery F

theorem factor_packet {F : Family} (A : Access F) (z : List Bool) (i k : ℕ) :
    factor A (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits
      ((((PolynomialKronecker.encode (F.radix (origin z)) (F.polynomial (origin z) i)).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus z) + 1)))).coeff k)) := by
  have hq : factorQuery F (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) =
      pair (pair (pair (origin z) (BinaryNatCode.encode i)) (modulus z))
        (pair (BinaryNatCode.encode (k % F.radix (origin z))) (BinaryNatCode.encode (k / F.radix (origin z)))) := by
    simp only [factorQuery, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair, BinaryNat.div_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [factor, Function.comp_apply, hq, A.reader.coefficient_eq, Polynomial.coeff_map,
    PolynomialKronecker.coefficient_any _ (F.radix_pos _) _ (F.factor_inner_lt _ i)]
  exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
    (by simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
    (by rw [pairSnd_pair])

def exponentQuery (q : List Bool) : List Bool := pair (origin (pairFst q)) (pairSnd q)
theorem exponentQuery_FP : exponentQuery ∈ FP := mem_FP_pair
  (mem_FP_comp (f := pairFst) (g := origin) pairFst_mem_FP origin_FP) pairSnd_mem_FP

noncomputable def countCode (F : Family) (z : List Bool) : List Bool := BinaryNatCode.encode (F.count (origin z))
noncomputable def selected (F : Family) (z : List Bool) : List Bool := BinaryNat.add
  (pair (innerWord z) (BinaryNat.mul (pair (BinaryNatCode.encode (F.radix (origin z))) (outerWord z))))

theorem selected_FP {F : Family} (A : Access F) : selected F ∈ FP := by
  have hr := mem_FP_comp origin_FP (radix_binary A).bits_mem_FP
  have hp := mem_FP_comp (mem_FP_pair hr outerWord_FP) BinaryNat.mul_mem_FP
  exact mem_FP_comp (mem_FP_pair innerWord_FP hp) BinaryNat.add_mem_FP

noncomputable def rawValue (F : Family) : List Bool → List Bool :=
  RootSignQueries.queryProductValue (countCode F) modulus (selected F)
    (fun z i => F.exponent (origin z) i)
    (fun z i => (PolynomialKronecker.encode (F.radix (origin z)) (F.polynomial (origin z) i)).map
      (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus z) + 1))))

theorem raw_evaluator {F : Family} (A : Access F) : SpaceFunction (rawValue F) := by
  have hc : BinaryFn (fun z => F.count (origin z)) := A.count_binary.comp origin_FP
  apply RootSignQueries.queryProductEvaluator
    (A.reader.evaluator.precompose (factorQuery F) (factorQuery_FP A))
    (countCode F) (A.exponent ∘ exponentQuery) modulus (selected F)
    hc.bits_mem_FP (mem_FP_comp exponentQuery_FP A.exponent_FP) modulus_FP (selected_FP A)
  · intro z i _
    simp only [Function.comp_apply, exponentQuery, pairFst_pair, pairSnd_pair]
    rw [A.exponent_eq]
    exact Nat.fromBitsLE_bits _
  · intro z i _ k
    exact factor_packet A z i k

theorem encoded_product (F : Family) (c : List Bool) :
    PolynomialKronecker.encode (F.radix c) (F.product c) =
      ∏ i ∈ Finset.range (F.count c), PolynomialKronecker.encode (F.radix c) (F.polynomial c i) ^ (F.exponent c i).val := by
  simp only [Family.product, RootSignQueries.queryPolynomial, map_prod, map_pow]
  exact Fin.prod_univ_eq_prod_range
    (fun i => PolynomialKronecker.encode (F.radix c) (F.polynomial c i) ^ (F.exponent c i).val) _

theorem raw_value_eq (F : Family) (z : List Bool) (hu : Nat.fromBitsLE (innerWord z) < F.radix (origin z)) :
    rawValue F z = residueBits ((((F.product (origin z)).coeff (Nat.fromBitsLE (outerWord z))).coeff
      (Nat.fromBitsLE (innerWord z)) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1)) := by
  rw [rawValue, RootSignQueries.queryProductValue]
  simp only [countCode, selected, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hp : (∏ i ∈ Finset.range (F.count (origin z)),
      ((PolynomialKronecker.encode (F.radix (origin z)) (F.polynomial (origin z) i)).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus z) + 1)))) ^ (F.exponent (origin z) i).val) =
      (PolynomialKronecker.encode (F.radix (origin z)) (F.product (origin z))).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus z) + 1))) := by
    rw [encoded_product]
    simp only [Polynomial.map_prod, Polynomial.map_pow]
  rw [hp, Polynomial.coeff_map, PolynomialKronecker.coefficient _ _ (F.product_inner_lt _) _ _ hu]
  rfl

noncomputable def within (F : Family) (z : List Bool) : Prop := Nat.fromBitsLE (innerWord z) < F.radix (origin z)
noncomputable instance (F : Family) (z : List Bool) : Decidable (within F z) := inferInstanceAs (Decidable (_ < _))
theorem within_pred {F : Family} (A : Access F) : FPPred (within F) :=
  (BinaryFn.fromBits innerWord_FP).lt ((radix_binary A).comp origin_FP)

noncomputable def value (F : Family) (z : List Bool) : List Bool := if within F z then rawValue F z else []

theorem evaluator {F : Family} (A : Access F) : SpaceFunction (value F) := by
  have E := SpaceFunction.branch (fun z => decide (within F z)) (within_pred A).flag_mem_FP
    (raw_evaluator A) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [value, decide_eq_true_eq])

theorem value_eq (F : Family) (z : List Bool) :
    value F z = residueBits ((((F.product (origin z)).coeff (Nat.fromBitsLE (outerWord z))).coeff
      (Nat.fromBitsLE (innerWord z)) : ℤ) : ZMod (Nat.fromBitsLE (modulus z) + 1)) := by
  by_cases hu : within F z
  · rw [value, ite_eq_left hu]
    exact raw_value_eq F z hu
  · rw [value, ite_eq_right hu, Polynomial.coeff_eq_zero_of_natDegree_lt
      ((F.product_inner_lt (origin z) _).trans_le (by unfold within at hu; omega))]
    simp [residueBits, BinaryNatCode.encode]

noncomputable def reader {F : Family} (A : Access F) : CertifiedPolynomial.BivariateReader F.product where
  coefficient := value F
  evaluator := evaluator A
  coefficient_eq q u v := by
    rw [value_eq]
    exact congrArg₂ (fun (a : ℤ) (m : ℕ) => residueBits (a : ZMod m))
      (by simp only [origin, innerWord, outerWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (by simp only [modulus, pairFst_pair])

end LeanCanny.Algebra.BivariateQueryProductBits
