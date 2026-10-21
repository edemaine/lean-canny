/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialAffineEntrySpace
public import LeanCanny.Algebra.BerkowitzPolynomialSpace

/-! # Affine deformation of a polynomial matrix in polynomial space

The original parameter and deformation parameter stay independent. A radix
above the determinant's full inner degree allows the polynomial backend to
recover their selected coefficient. Entry access is supplied internally from
one original coefficient call and a degree-zero diagonal test.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzAffinePolynomial
open Complexity LeanCanny.Encoding LeanCanny.Computation
open MatrixPower
open scoped BigOperators Classical

structure Family where
  source : BerkowitzPolynomial.ModularFamily
  inner : List Bool → ℕ
  outer : List Bool → ℕ
  bound : List Bool → ℕ
  entry_degree : ∀ c r s, (source.matrix c r s).natDegree ≤ bound c

def Family.radix (F : Family) (c : List Bool) : ℕ := F.source.dimension c * F.bound c + 1

theorem Family.radix_pos (F : Family) (c : List Bool) : 0 < F.radix c := by unfold Family.radix; omega

theorem Family.entry_lt_radix (F : Family) (c : List Bool) (r s : Fin (F.source.dimension c)) :
    (F.source.matrix c r s).natDegree < F.radix c := by
  have hdim : 1 ≤ F.source.dimension c := by have h := r.isLt; omega
  have h := Nat.mul_le_mul_right (F.bound c) hdim
  simp only [one_mul] at h
  exact (F.entry_degree c r s).trans_lt (by unfold Family.radix; omega)

noncomputable def Family.matrix (F : Family) (c : List Bool) :
    Matrix (Fin (F.source.dimension c)) (Fin (F.source.dimension c)) (Polynomial (Polynomial (ZMod (F.source.modulus c)))) :=
  fun r s => PolynomialAffineDeformation.affine (F.source.matrix c r s) (if r = s then 1 else 0)

theorem Family.matrix_bound (F : Family) (c : List Bool) (r s : Fin (F.source.dimension c)) (j : ℕ) :
    ((F.matrix c r s).coeff j).natDegree ≤ F.bound c :=
  PolynomialAffineDeformation.inner_degree_le _ _ _ (F.entry_degree c r s) j

theorem Family.determinant_bound (F : Family) (c : List Bool) (j : ℕ) :
    ((F.matrix c).det.coeff j).natDegree ≤ F.source.dimension c * F.bound c := by
  have h := PolynomialKronecker.determinant_inner_degree (F.matrix c) (fun _ => F.bound c) (F.matrix_bound c) j
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using h

noncomputable def Family.encoded (F : Family) : BerkowitzPolynomial.ModularFamily where
  dimension := F.source.dimension
  modulus := F.source.modulus
  degree c := F.inner c + F.radix c * F.outer c
  matrix c := (F.matrix c).map (PolynomialKronecker.encode (F.radix c))
  modulus_ne_zero := F.source.modulus_ne_zero

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c))

theorem Family.encoded_value (F : Family) (c : List Bool) (hi : F.inner c < F.radix c) :
    F.encoded.value c = F.value c := by
  change residueBits (((F.matrix c).map (PolynomialKronecker.encode (F.radix c))).det.coeff (F.inner c + F.radix c * F.outer c)) = _
  have h := PolynomialKronecker.determinant_coefficient (F.matrix c) (fun _ => F.bound c) (F.matrix_bound c)
    (F.radix c) (by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; exact Nat.lt_succ_self _)
    (F.inner c) (F.outer c) hi
  exact congrArg residueBits h

theorem Family.value_zero (F : Family) (c : List Bool) (hi : ¬F.inner c < F.radix c) : F.value c = [] := by
  have hd := F.determinant_bound c (F.outer c)
  have hz : ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    unfold Family.radix at hi
    omega
  simp [Family.value, hz, residueBits, BinaryNatCode.encode]

structure Access (F : Family) where
  original : BerkowitzPolynomial.ModularAccess F.source
  inner : List Bool → List Bool
  outer : List Bool → List Bool
  bound : List Bool → List Bool
  inner_eq : ∀ c, inner c = BinaryNatCode.encode (F.inner c)
  outer_eq : ∀ c, outer c = BinaryNatCode.encode (F.outer c)
  bound_eq : ∀ c, bound c = BinaryNatCode.encode (F.bound c)

def Access.radixCode {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.mul (pair (a.original.dimension c) (a.bound c)))

theorem Access.radixCode_mem_FP {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP) (hb : a.bound ∈ FP) : a.radixCode ∈ FP := by
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hN hb) BinaryNat.mul_mem_FP) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq (g := a.radixCode) h (fun _ => by simp only [Access.radixCode, Function.comp_apply])

theorem Access.radixCode_eq {F : Family} (a : Access F) (c : List Bool) : a.radixCode c = BinaryNatCode.encode (F.radix c) := by
  simp only [Access.radixCode, a.original.dimension_eq, a.bound_eq, BinaryNat.mul_pair, BinaryNat.succ_eq_bits,
    MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]
  rfl

def Access.degreeCode {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.inner c) (BinaryNat.mul (pair (a.radixCode c) (a.outer c))))

theorem Access.degreeCode_mem_FP {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP) (hb : a.bound ∈ FP)
    (hi : a.inner ∈ FP) (ho : a.outer ∈ FP) : a.degreeCode ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair hi (mem_FP_comp (mem_FP_pair (a.radixCode_mem_FP hN hb) ho) BinaryNat.mul_mem_FP)) BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := a.degreeCode) h (fun _ => by simp only [Access.degreeCode, Function.comp_apply])

theorem Access.degreeCode_eq {F : Family} (a : Access F) (c : List Bool) : a.degreeCode c = BinaryNatCode.encode (F.encoded.degree c) := by
  simp only [Access.degreeCode, a.inner_eq, a.outer_eq, a.radixCode_eq, BinaryNat.add_pair, BinaryNat.mul_pair,
    MacaulayBits.fromBits_encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def Access.encoded {F : Family} (a : Access F) : BerkowitzPolynomial.ModularAccess F.encoded where
  dimension := a.original.dimension
  modulus := a.original.modulus
  degree := a.degreeCode
  entry := PolynomialAffineEntryBits.value a.original.modulus a.radixCode a.original.entry
  dimension_eq := a.original.dimension_eq
  modulus_eq := a.original.modulus_eq
  degree_eq := a.degreeCode_eq
  entry_eq c r s d := by
    change Fin (F.source.dimension c) at r s
    have h := PolynomialAffineEntryBits.value_packet a.original.modulus a.radixCode a.original.entry c r.val s.val d
      (F.source.modulus c) (F.radix c) (a.original.modulus_eq c) (a.radixCode_eq c)
      (Nat.pos_of_ne_zero (F.source.modulus_ne_zero c)) (F.radix_pos c) (F.source.matrix c r s)
      (F.entry_lt_radix c r s) (fun k => a.original.entry_eq c r s k)
    have hdelta : (if r.val = s.val then (1 : ZMod (F.source.modulus c)) else 0) = (if r = s then 1 else 0) := by
      simp only [Fin.ext_iff]
    rw [hdelta] at h
    exact h

attribute [local irreducible] PolynomialAffineEntryBits.value

theorem Access.entryEvaluator {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP)
    (hm : a.original.modulus ∈ FP) (hb : a.bound ∈ FP) (E : SpaceFunction a.original.entry) : SpaceFunction a.encoded.entry := by
  have ES := PolynomialAffineEntryBits.evaluator E hm (a.radixCode_mem_FP hN hb)
  change SpaceFunction (PolynomialAffineEntryBits.value a.original.modulus a.radixCode a.original.entry)
  exact ES

theorem Access.encoded_controls {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP)
    (hm : a.original.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP) : a.encoded.ControlsPolyTime :=
  ⟨hN, hm, a.degreeCode_mem_FP hN hb hi ho⟩

theorem Access.valid_fppred {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP)
    (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) : FPPred (fun c => F.inner c < F.radix c) :=
  (BinaryNat.lt_fppred hi (a.radixCode_mem_FP hN hb)).of_iff (fun c => by
    simp only [a.inner_eq, a.radixCode_eq, MacaulayBits.fromBits_encode])

theorem Access.evaluator {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP)
    (hm : a.original.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP)
    (E : SpaceFunction a.original.entry) : SpaceFunction F.value := by
  have ES := BerkowitzPolynomial.ModularAccess.evaluator a.encoded (a.encoded_controls hN hm hb hi ho) (a.entryEvaluator hN hm hb E)
  have EB := SpaceFunction.branch (fun c => decide (F.inner c < F.radix c)) (a.valid_fppred hN hb hi).flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hc
  · exact F.encoded_value c hc
  · exact (F.value_zero c hc).symm

def Family.zeroLanguage (F : Family) : Language :=
  {c | ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0}

theorem Access.zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (hN : a.original.dimension ∈ FP)
    (hm : a.original.modulus ∈ FP) (hb : a.bound ∈ FP) (hi : a.inner ∈ FP) (ho : a.outer ∈ FP)
    (E : SpaceFunction a.original.entry) : F.zeroLanguage ∈ PSPACE := by
  have ES := a.evaluator hN hm hb hi ho E
  have EA := (Encoding.Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply SpaceDecider.mem_PSPACE
  refine ES.decider (fun z => decide (z = [])) EA ?_
  intro c
  let : NeZero (F.source.modulus c) := ⟨F.source.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.source.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0 ↔
    decide (residueBits (((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c)) = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.source.modulus c)).eq_iff]

end LeanCanny.Algebra.BerkowitzAffinePolynomial
