/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullBoxFinite
public import LeanCanny.Algebra.BerkowitzPolynomialSpace
public import LeanCanny.Algebra.PolynomialKronecker

/-! # Bivariate determinant coefficients with binary matrix dimensions

This generic backend accepts a native bivariate matrix entry reader. The
canonical full-box block matrix is a particular input; no selected minor or
stored matrix is required.
-/

@[expose] public section

namespace LeanCanny.Algebra.BivariateDeterminantBits
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

structure Family where
  dimension : List Bool → ℕ
  dimension_pos : ∀ c, 0 < dimension c
  modulus : List Bool → ℕ
  inner : List Bool → ℕ
  outer : List Bool → ℕ
  bound : List Bool → ℕ
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c))
    (Polynomial (Polynomial (ZMod (modulus c))))
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  inner_bound : ∀ c i j k, (((matrix c i j).coeff k).natDegree) ≤ bound c

def Family.radix (F : Family) (c : List Bool) : ℕ := F.dimension c * F.bound c + 1

theorem Family.radix_pos (F : Family) (c : List Bool) : 0 < F.radix c := by unfold Family.radix; omega

theorem Family.bound_lt_radix (F : Family) (c : List Bool) : F.bound c < F.radix c := by
  have hdim : 1 ≤ F.dimension c := F.dimension_pos c
  have h := Nat.mul_le_mul_right (F.bound c) hdim
  simp only [one_mul] at h
  unfold Family.radix
  omega

theorem Family.determinant_bound (F : Family) (c : List Bool) (j : ℕ) :
    (((F.matrix c).det.coeff j).natDegree) ≤ F.dimension c * F.bound c := by
  have h := PolynomialKronecker.determinant_inner_degree (F.matrix c) (fun _ => F.bound c) (F.inner_bound c) j
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

noncomputable def Family.encoded (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension := F.dimension
  modulus := F.modulus
  degree c := F.inner c + F.radix c * F.outer c
  matrix c := (F.matrix c).map (PolynomialKronecker.encode (F.radix c))
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c))

theorem Family.encoded_value (F : Family) (c : List Bool) (hi : F.inner c < F.radix c) :
    F.encoded.value c = F.value c := by
  change residueBits ((F.encoded.matrix c).det.coeff (F.inner c + F.radix c * F.outer c)) = _
  change residueBits (((F.matrix c).map (PolynomialKronecker.encode (F.radix c))).det.coeff _) = _
  have hc := PolynomialKronecker.determinant_coefficient (F.matrix c) (fun _ => F.bound c) (F.inner_bound c)
    (F.radix c) (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; exact Nat.lt_succ_self _)
    (F.inner c) (F.outer c) hi
  exact congrArg residueBits hc

theorem Family.value_zero (F : Family) (c : List Bool) (hi : ¬F.inner c < F.radix c) : F.value c = [] := by
  have hd := F.determinant_bound c (F.outer c)
  have hz : ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    unfold Family.radix at hi
    omega
  simp [Family.value, hz, residueBits, BinaryNatCode.encode]

structure Access (F : Family) where
  dimension : List Bool → List Bool
  modulus : List Bool → List Bool
  inner : List Bool → List Bool
  outer : List Bool → List Bool
  bound : List Bool → List Bool
  coefficient : List Bool → List Bool
  dimension_eq : ∀ c, dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  inner_eq : ∀ c, inner c = BinaryNatCode.encode (F.inner c)
  outer_eq : ∀ c, outer c = BinaryNatCode.encode (F.outer c)
  bound_eq : ∀ c, bound c = BinaryNatCode.encode (F.bound c)
  coefficient_eq : ∀ c (i j : Fin (F.dimension c)) u v,
    coefficient (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
        residueBits ((((F.matrix c i j).coeff v).coeff u))

def Access.radixCode {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.mul (pair (a.dimension c) (a.bound c)))

theorem Access.radixCode_mem_FP {F : Family} (a : Access F) (hn : a.dimension ∈ FP) (hb : a.bound ∈ FP) : a.radixCode ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_pair hn hb) BinaryNat.mul_mem_FP) BinaryNat.succ_mem_FP

theorem Access.radixCode_eq {F : Family} (a : Access F) (c : List Bool) :
    a.radixCode c = BinaryNatCode.encode (F.radix c) := by
  simp only [Access.radixCode, a.dimension_eq, a.bound_eq,
    BinaryNat.mul_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

def Access.degreeCode {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.inner c) (BinaryNat.mul (pair (a.radixCode c) (a.outer c))))

theorem Access.degreeCode_mem_FP {F : Family} (a : Access F) (hn : a.dimension ∈ FP)
    (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP) : a.degreeCode ∈ FP := by
  have hc := mem_FP_comp (mem_FP_pair hi (mem_FP_comp (mem_FP_pair (a.radixCode_mem_FP hn hb) ho) BinaryNat.mul_mem_FP)) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := a.degreeCode) hc (fun _ => by simp only [Access.degreeCode, Function.comp_apply])

theorem Access.degreeCode_eq {F : Family} (a : Access F) (c : List Bool) :
    a.degreeCode c = BinaryNatCode.encode (F.encoded.degree c) := by
  simp only [Access.degreeCode, a.inner_eq, a.outer_eq, a.radixCode_eq,
    BinaryNat.mul_pair, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

def Access.coefficientInput {F : Family} (a : Access F) (q : List Bool) : List Bool :=
  let uv := BinaryNat.divMod (pair (pairSnd (pairSnd (pairSnd q))) (a.radixCode (pairFst q)))
  pair (pairFst q) (pair (pairFst (pairSnd q))
    (pair (pairFst (pairSnd (pairSnd q))) (pair (pairSnd uv) (pairFst uv))))

theorem Access.coefficientInput_mem_FP {F : Family} (a : Access F) (hn : a.dimension ∈ FP)
    (hb : a.bound ∈ FP) : a.coefficientInput ∈ FP := by
  have ht := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp ht pairFst_mem_FP
  have hd := mem_FP_comp ht pairSnd_mem_FP
  have hB := mem_FP_comp pairFst_mem_FP (a.radixCode_mem_FP hn hb)
  have huv := mem_FP_comp (mem_FP_pair hd hB) BinaryNat.divMod_mem_FP
  have hc := mem_FP_pair pairFst_mem_FP (mem_FP_pair hi (mem_FP_pair hr
    (mem_FP_pair (mem_FP_comp huv pairSnd_mem_FP) (mem_FP_comp huv pairFst_mem_FP))))
  exact mem_FP_of_eq (g := a.coefficientInput) hc (fun _ => by simp only [Access.coefficientInput, Function.comp_apply])

theorem Access.coefficientInput_packet {F : Family} (a : Access F) (c : List Bool) (i k d : ℕ) :
    a.coefficientInput (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode d)))) =
      pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode (d % F.radix c)) (BinaryNatCode.encode (d / F.radix c))))) := by
  simp only [Access.coefficientInput, pairFst_pair, pairSnd_pair, a.radixCode_eq, BinaryNat.divMod_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def Access.encoded {F : Family} (a : Access F) : BerkowitzPolynomial.ModularAccess F.encoded where
  dimension := a.dimension
  modulus := a.modulus
  degree := a.degreeCode
  entry := a.coefficient ∘ a.coefficientInput
  dimension_eq := a.dimension_eq
  modulus_eq := a.modulus_eq
  degree_eq := a.degreeCode_eq
  entry_eq c i k d := by
    change Fin (F.dimension c) at i
    change a.coefficient (a.coefficientInput _) = _
    rw [a.coefficientInput_packet, a.coefficient_eq c i k (d % F.radix c) (d / F.radix c)]
    change residueBits _ = residueBits ((PolynomialKronecker.encode (F.radix c) (F.matrix c i k)).coeff d)
    rw [PolynomialKronecker.coefficient_any (F.radix c) (F.radix_pos c) _
      (fun j => (F.inner_bound c i k j).trans_lt (F.bound_lt_radix c))]

theorem Access.valid_fppred {F : Family} (a : Access F) (hn : a.dimension ∈ FP)
    (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) : FPPred (fun c => F.inner c < F.radix c) :=
  (BinaryNat.lt_fppred hi (a.radixCode_mem_FP hn hb)).of_iff (fun c => by
    simp only [a.inner_eq, a.radixCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem Access.evaluator {F : Family} (a : Access F) (hn : a.dimension ∈ FP)
    (hm : a.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP)
    (E : SpaceFunction a.coefficient) : SpaceFunction F.value := by
  have EC := E.precompose a.coefficientInput (a.coefficientInput_mem_FP hn hb)
  have ES := BerkowitzPolynomial.ModularAccess.evaluator a.encoded
    ⟨hn, hm, a.degreeCode_mem_FP hn hb hi ho⟩ EC
  have EB := SpaceFunction.branch (fun c => decide (F.inner c < F.radix c)) (a.valid_fppred hn hb hi).flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hc
  · exact F.encoded_value c hc
  · exact (F.value_zero c hc).symm



end LeanCanny.Algebra.BivariateDeterminantBits
