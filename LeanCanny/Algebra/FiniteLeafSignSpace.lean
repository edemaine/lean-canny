/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignSource

/-! # Polynomial-space feasibility of streamed signs on finite root tuples -/

@[expose] public section
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace LeanCanny.Algebra.FiniteLeafSignBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution
open SeparableBits (Family Readers)
open scoped Classical
attribute [local irreducible] FiniteLeafCoordinateBits.coordinate

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

/-- Degree and mass bounds for all the substituted constraint rows. -/
def signDegree (S : Source count) (c : List Bool) : ℕ :=
  count c * (2 * S.degree c) * coordinateDegree count D b c

def signMass (S : Source count) (c : List Bool) : ℕ :=
  (S.terms c).size + S.height c + count c * (2 * S.degree c) * coordinateMass count D b c

include hdegree hheight in
theorem substituted_bounds (S : Source count) (c : List Bool) (j : ℕ) :
    ((substitution B count D b hne S).polynomial (pair c (BinaryNatCode.encode j))).natDegree ≤ signDegree count D b S c ∧
    coefficientMass ((substitution B count D b hne S).polynomial (pair c (BinaryNatCode.encode j))) ≤ 2 ^ signMass count D b S c := by
  simp only [IntegerBits.Family.polynomial, substitution, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j, signDegree, signMass]
  have hnq : numerator B count D b hne (pair c (BinaryNatCode.encode j)) = numerator B count D b hne (pair c []) := by
    funext i
    simp only [numerator, pairFst_pair]
  have hdq : denominator B count D b hne (pair c (BinaryNatCode.encode j)) = denominator B count D b hne (pair c []) := by
    funext i
    simp only [denominator, pairFst_pair]
  rw [hnq, hdq]
  have H := coordinate_bounds B count D b hne hdegree hheight c
  exact ⟨Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _ (S.exponent_le c j)
      (fun i _ => (H i).1) (fun i _ => (H i).2.1),
    Indexed.coefficientMass_cleared_le_pow _ _ _ _ _ _ _ _ _ (S.exponent_le c j)
      (S.coefficient_le c j) (fun i _ => (H i).2.2.1) (fun i _ => (H i).2.2.2)⟩

include hdegree hheight in
noncomputable def signFamily (S : Source count) : SignPatternBits.Family where
  root := FiniteAnnihilatorBits.finiteParameter B count hne
  polynomial c j := (substitution B count D b hne S).polynomial (pair c (BinaryNatCode.encode j))
  pattern := S.pattern
  count c := BinaryNatCode.encode (S.count c)
  rootDegree c := BinaryNatCode.encode (D c ^ count c + 1)
  degree c := BinaryNatCode.encode (signDegree count D b S c)
  rootMass c := BinaryNatCode.encode (FiniteAnnihilatorTree.sourceHeight (D c) (b c) (count c))
  mass c := BinaryNatCode.encode (signMass count D b S c)
  rootDegree_pos c := by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega
  root_degree c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (FiniteAnnihilatorTree.parameter_degree_le _ _ _ (D c) (hdegree c)).trans (Nat.le_add_right _ _)
  root_mass c := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact FiniteAnnihilatorTree.parameter_mass_from_source _ _ _ (D c) (b c) (hdegree c)
      (fun i hi k => (B.coefficient_bound _ k).trans (Nat.pow_le_pow_right (by decide) (hheight c i hi)))
  polynomial_degree c j _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using (substituted_bounds B count D b hne hdegree hheight S c j).1
  polynomial_mass c j _ := by
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using (substituted_bounds B count D b hne hdegree hheight S c j).2

attribute [local irreducible] FiniteAnnihilatorTree.sourceHeight

include hdegree hheight in
theorem signControls (S : Source count) (A : S.Access) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SignPatternBits.ControlsPolyTime (signFamily B count D b hne hdegree hheight S) := by
  have hc : BinaryFn count := BinaryFn.of_bits (bits_mem_FP hn)
  have hd := coordinateDegree_binary count D b hn hD hb
  have hm := coordinateMass_binary count D b hn hD hb
  have hs : BinaryFn (fun c => (S.terms c).size + S.height c) :=
    BinaryFn.add (BinaryFn.size A.terms_binary) A.height_binary
  have hx : BinaryFn (fun c => count c * (2 * S.degree c) * coordinateMass count D b c) :=
    BinaryFn.mul (BinaryFn.mul hc (BinaryFn.mul (BinaryFn.const 2) A.degree_binary)) hm
  have hmass : BinaryFn (signMass count D b S) := BinaryFn.add hs hx
  have hr : BinaryFn (fun c => FiniteAnnihilatorTree.sourceHeight (D c) (b c) (count c)) :=
    FiniteAnnihilatorTree.sourceHeight_binary hD hb hn
  constructor
  · exact bits_mem_FP A.count_unary
  · change UnaryFn (fun c => Nat.fromBitsLE (BinaryNatCode.encode (S.count c)))
    exact A.count_unary.of_eq (fun c => (Nat.fromBitsLE_bits (S.count c)).symm)
  · exact ((hD.powUnary hn).add (BinaryFn.const 1)).bits_mem_FP
  · exact ((hc.mul ((BinaryFn.const 2).mul A.degree_binary)).mul hd).bits_mem_FP
  · change (fun c => BinaryNatCode.encode (FiniteAnnihilatorTree.sourceHeight (D c) (b c) (count c))) ∈ FP
    exact hr.bits_mem_FP
  · change (fun c => BinaryNatCode.encode (signMass count D b S c)) ∈ FP
    exact hmass.bits_mem_FP

def polynomialQuery (q : List Bool) : List Bool :=
  pair (pair (pair (IntegerBits.context q) (pairFst (IntegerBits.selectedDegree q)))
    (pairSnd (IntegerBits.selectedDegree q))) (pairSnd q)

theorem polynomialQuery_FP : polynomialQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair IntegerBits.context_mem_FP
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

include hdegree hheight in
noncomputable def signAccess (S : Source count) (A : S.Access) :
    SignPatternBits.Access (signFamily B count D b hne hdegree hheight S) where
  rootCoefficient := FiniteAnnihilatorBits.coefficient B count hne
  polynomialCoefficient := (substitution B count D b hne S).value ∘ polynomialQuery
  pattern := A.pattern
  root_eq c k m hm := by
    simp only [FiniteAnnihilatorBits.coefficient, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl
  polynomial_eq c i _ k m hm := by
    simp only [Function.comp_apply, polynomialQuery, IntegerBits.context, IntegerBits.selectedDegree,
      IntegerBits.Family.value, IntegerBits.mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl
  pattern_eq := A.pattern_eq

include hdegree hheight in
theorem signRealizable_mem_PSPACE (S : Source count) (A : S.Access) (R : Readers B)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SignPatternBits.realizableLanguage (signFamily B count D b hne hdegree hheight S) ∈ PSPACE := by
  apply SignPatternBits.realizableLanguage_mem_PSPACE (signAccess B count D b hne hdegree hheight S A)
    (signControls B count D b hne hdegree hheight S A hn hD hb) A.pattern_FP
    (FiniteAnnihilatorBits.coefficientEvaluator B R count D b hn hD hb hne hdegree hheight)
    ((substitutionEvaluator B count D b hne hdegree hheight S A R hn hD hb).precompose _ polynomialQuery_FP)
  intro c
  exact (FiniteAnnihilatorTree.parameter _ _ _).ne_zero

include hdegree hheight in
theorem substituted_sign (S : Source count) (c : List Bool) (j : ℕ) (theta : ℝ)
    (ht : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign (((substitution B count D b hne S).polynomial (pair c (BinaryNatCode.encode j))).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((S.polynomial c j).eval₂ (Int.castRingHom ℝ)
        (FiniteAnnihilatorTree.decode (fun i => B.polynomial (pair c (BinaryNatCode.encode i))) (count c) (hne c) theta)) := by
  have H := Indexed.sign_eval₂_cleared (Int.castRingHom ℝ) theta (count c) (S.terms c) (S.degree c)
    (S.coefficient c j) (S.exponent c j) (numerator B count D b hne (pair c []))
    (denominator B count D b hne (pair c [])) (S.exponent_le c j)
    (fun i hi => by
      simpa only [denominator, pairFst_pair] using
        (FiniteLeafCoordinateBits.finite_decode_spec B count D b hne hdegree hheight c ⟨i, hi⟩ theta ht).1)
  simp only [IntegerBits.Family.polynomial, substitution, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]
  have hnq : numerator B count D b hne (pair c (BinaryNatCode.encode j)) = numerator B count D b hne (pair c []) := by
    funext i
    simp only [numerator, pairFst_pair]
  have hdq : denominator B count D b hne (pair c (BinaryNatCode.encode j)) = denominator B count D b hne (pair c []) := by
    funext i
    simp only [denominator, pairFst_pair]
  rw [hnq, hdq]
  rw [H]
  congr 1
  congr 1
  funext i
  simpa only [numerator, denominator, pairFst_pair, UnivariateRational.Coordinate.eval] using
    (FiniteLeafCoordinateBits.finite_decode_spec B count D b hne hdegree hheight c i theta ht).2

/-- Real tuples of original annihilator roots satisfying all streamed signs. -/
def finiteSignLanguage (S : Source count) : Language := {c |
  ∃ x : Fin (count c) → ℝ,
    (∀ i, (B.polynomial (pair c (BinaryNatCode.encode i.val))).eval₂ (Int.castRingHom ℝ) (x i) = 0) ∧
    ∀ j : Fin (S.count c), SignType.sign ((S.polynomial c j.val).eval₂ (Int.castRingHom ℝ) x) = S.pattern c j.val}

include hdegree hheight in
theorem finiteSignLanguage_eq (S : Source count) :
    finiteSignLanguage B count S = SignPatternBits.realizableLanguage (signFamily B count D b hne hdegree hheight S) := by
  ext c
  change (∃ x : Fin (count c) → ℝ, _ ∧ _) ↔ _
  constructor
  · rintro ⟨x, hx, hs⟩
    let theta := FiniteAnnihilatorTree.encode (fun i => B.polynomial (pair c (BinaryNatCode.encode i))) (count c) (hne c) x
    have ht := FiniteAnnihilatorTree.encode_root (fun i => B.polynomial (pair c (BinaryNatCode.encode i))) (count c) (hne c) x hx
    refine ⟨theta, ?_, ?_⟩
    · simpa only [Polynomial.eval_map, algebraMap_int_eq, signFamily, FiniteAnnihilatorBits.finiteParameter] using ht
    · intro j
      have hj : j.val < S.count c := by simpa only [signFamily, BinaryNatCode.encode, Nat.fromBitsLE_bits] using j.isLt
      rw [show (signFamily B count D b hne hdegree hheight S).polynomial c j.val =
        (substitution B count D b hne S).polynomial (pair c (BinaryNatCode.encode j.val)) from rfl]
      rw [Polynomial.eval_map, algebraMap_int_eq, substituted_sign B count D b hne hdegree hheight S c j.val theta ht]
      rw [FiniteAnnihilatorTree.decode_encode _ _ _ x hx]
      exact hs ⟨j.val, hj⟩
  · rintro ⟨theta, ht, hs⟩
    have ht' : (FiniteAnnihilatorBits.finiteParameter B count hne c).eval₂ (Int.castRingHom ℝ) theta = 0 := by
      simpa only [Polynomial.eval_map, algebraMap_int_eq, signFamily] using ht
    refine ⟨FiniteAnnihilatorTree.decode _ _ (hne c) theta,
      FiniteAnnihilatorTree.decode_root _ _ _ theta ht', ?_⟩
    intro j
    have hj : j.val < Nat.fromBitsLE ((signFamily B count D b hne hdegree hheight S).count c) := by
      simpa only [signFamily, BinaryNatCode.encode, Nat.fromBitsLE_bits] using j.isLt
    have H := hs ⟨j.val, hj⟩
    rw [Polynomial.eval_map, algebraMap_int_eq] at H
    exact (substituted_sign B count D b hne hdegree hheight S c j.val theta ht').symm.trans H

include hne hdegree hheight in
theorem finiteSignLanguage_mem_PSPACE (S : Source count) (A : S.Access) (R : Readers B)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) : finiteSignLanguage B count S ∈ PSPACE := by
  rw [finiteSignLanguage_eq B count D b hne hdegree hheight S]
  exact signRealizable_mem_PSPACE B count D b hne hdegree hheight S A R hn hD hb

end LeanCanny.Algebra.FiniteLeafSignBits
