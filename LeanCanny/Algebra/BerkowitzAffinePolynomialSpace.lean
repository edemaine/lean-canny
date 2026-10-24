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
open LeanCanny.Encoding LeanCanny.Computation
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

/-- Canonical encodings need no separate word writers or field-equality proofs. -/
noncomputable def Family.encodedAccess (F : Family) (a : BerkowitzPolynomial.ModularAccess F.source) :
    BerkowitzPolynomial.ModularAccess F.encoded where
  dimension c := BinaryNatCode.encode (F.source.dimension c)
  modulus := a.modulus
  degree c := BinaryNatCode.encode (F.encoded.degree c)
  entry := PolynomialAffineEntryBits.value a.modulus (fun c => BinaryNatCode.encode (F.radix c)) a.entry
  dimension_eq _ := rfl
  modulus_eq := a.modulus_eq
  degree_eq _ := rfl
  entry_eq c r s d := by
    change Fin (F.source.dimension c) at r s
    have h := PolynomialAffineEntryBits.value_packet a.modulus (fun c => BinaryNatCode.encode (F.radix c)) a.entry c r.val s.val d
      (F.source.modulus c) (F.radix c) (a.modulus_eq c) rfl
      (Nat.pos_of_ne_zero (F.source.modulus_ne_zero c)) (F.radix_pos c) (F.source.matrix c r s)
      (F.entry_lt_radix c r s) (fun k => a.entry_eq c r s k)
    have hdelta : (if r.val = s.val then (1 : ZMod (F.source.modulus c)) else 0) = (if r = s then 1 else 0) := by
      simp only [Fin.ext_iff]
    rw [hdelta] at h
    exact h

attribute [local irreducible] PolynomialAffineEntryBits.value

theorem Family.evaluator (F : Family) (a : BerkowitzPolynomial.ModularAccess F.source)
    (hN : BinaryFn F.source.dimension) (hm : a.modulus ∈ FP)
    (hb : BinaryFn F.bound) (hi : BinaryFn F.inner) (ho : BinaryFn F.outer)
    (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have hr : BinaryFn F.radix := (hN.mul hb).add (BinaryFn.const 1)
  have hd : BinaryFn F.encoded.degree := hi.add (hr.mul ho)
  have EE := PolynomialAffineEntryBits.evaluator E hm hr.bits_mem_FP
  have ES := BerkowitzPolynomial.ModularAccess.evaluator (F.encodedAccess a)
    ⟨hN.bits_mem_FP, hm, hd.bits_mem_FP⟩ EE
  have EB := SpaceFunction.branch (fun c => decide (F.inner c < F.radix c)) (hi.lt hr).flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hc
  · exact F.encoded_value c hc
  · exact (F.value_zero c hc).symm

def Family.zeroLanguage (F : Family) : Language :=
  {c | ((F.matrix c).det.coeff (F.outer c)).coeff (F.inner c) = 0}

theorem Family.zeroLanguage_mem_PSPACE (F : Family) (a : BerkowitzPolynomial.ModularAccess F.source)
    (hN : BinaryFn F.source.dimension) (hm : a.modulus ∈ FP)
    (hb : BinaryFn F.bound) (hi : BinaryFn F.inner) (ho : BinaryFn F.outer)
    (E : SpaceFunction a.entry) : F.zeroLanguage ∈ PSPACE := by
  have ES := F.evaluator a hN hm hb hi ho E
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
