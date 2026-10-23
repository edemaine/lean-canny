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

/-- The Kronecker radix is written in binary, even for exponential dimensions. -/
theorem Family.radix_binary (F : Family) (hn : BinaryFn F.dimension)
    (hb : BinaryFn F.bound) : BinaryFn F.radix :=
  (hn.mul hb).add (BinaryFn.const 1)

def Family.coefficientInput (F : Family) (q : List Bool) : List Bool :=
  let uv := BinaryNat.divMod (pair (pairSnd (pairSnd (pairSnd q)))
    (BinaryNatCode.encode (F.radix (pairFst q))))
  pair (pairFst q) (pair (pairFst (pairSnd q))
    (pair (pairFst (pairSnd (pairSnd q))) (pair (pairSnd uv) (pairFst uv))))

theorem Family.coefficientInput_mem_FP (F : Family) (hn : BinaryFn F.dimension)
    (hb : BinaryFn F.bound) : F.coefficientInput ∈ FP := by
  have ht := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp ht pairFst_mem_FP
  have hd := mem_FP_comp ht pairSnd_mem_FP
  have hB := mem_FP_comp pairFst_mem_FP (F.radix_binary hn hb).bits_mem_FP
  have huv := mem_FP_comp (mem_FP_pair hd hB) BinaryNat.divMod_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair hi (mem_FP_pair hr
    (mem_FP_pair (mem_FP_comp huv pairSnd_mem_FP) (mem_FP_comp huv pairFst_mem_FP))))

theorem Family.coefficientInput_packet (F : Family) (c : List Bool) (i k d : ℕ) :
    F.coefficientInput (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k) (BinaryNatCode.encode d)))) =
      pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode k)
        (pair (BinaryNatCode.encode (d % F.radix c)) (BinaryNatCode.encode (d / F.radix c))))) := by
  simp only [Family.coefficientInput, pairFst_pair, pairSnd_pair, BinaryNat.divMod_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

/-- Canonical binary controls remove the redundant writer/equality layer. The
entry certificate still accepts an arbitrary native polynomial-space child. -/
theorem Family.evaluator (F : Family) (coefficient : List Bool → List Bool)
    (hc : ∀ c (i j : Fin (F.dimension c)) u v,
      coefficient (pair c (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
          residueBits (((F.matrix c i j).coeff v).coeff u))
    (hn : BinaryFn F.dimension) (hm : BinaryFn F.modulus) (hb : BinaryFn F.bound)
    (hi : BinaryFn F.inner) (ho : BinaryFn F.outer) (E : SpaceFunction coefficient) :
    SpaceFunction F.value := by
  let a : BerkowitzPolynomial.ModularAccess F.encoded := {
    dimension := fun c => BinaryNatCode.encode (F.dimension c)
    modulus := fun c => BinaryNatCode.encode (F.modulus c)
    degree := fun c => BinaryNatCode.encode (F.encoded.degree c)
    entry := coefficient ∘ F.coefficientInput
    dimension_eq _ := rfl
    modulus_eq _ := rfl
    degree_eq _ := rfl
    entry_eq c i k d := by
      change Fin (F.dimension c) at i
      change coefficient (F.coefficientInput _) = _
      rw [F.coefficientInput_packet, hc c i k (d % F.radix c) (d / F.radix c)]
      change residueBits _ = residueBits ((PolynomialKronecker.encode (F.radix c) (F.matrix c i k)).coeff d)
      rw [PolynomialKronecker.coefficient_any (F.radix c) (F.radix_pos c) _
        (fun j => (F.inner_bound c i k j).trans_lt (F.bound_lt_radix c))] }
  have hr := F.radix_binary hn hb
  have ES := a.evaluator ⟨hn.bits_mem_FP, hm.bits_mem_FP, (hi.add (hr.mul ho)).bits_mem_FP⟩
    (E.precompose F.coefficientInput (F.coefficientInput_mem_FP hn hb))
  have EB := SpaceFunction.branch (fun c => decide (F.inner c < F.radix c)) (hi.lt hr).flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hc
  · exact F.encoded_value c hc
  · exact (F.value_zero c hc).symm

end LeanCanny.Algebra.BivariateDeterminantBits
