/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledSquarefreeBounds
public import LeanCanny.Computation.SpaceFunctionSpaceBranch

/-! # Total polynomial contexts with a checked stored degree

Contexts pair an original input with a declared degree. Correct degrees retain
the source polynomial; incorrect degrees select a separable polynomial of the
declared degree. Thus degree metadata is FP and exact on every binary context,
even when computing the source's degree needs polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.ValidatedDegreeBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open PrincipalCoefficientBits (integerResidue)
open scoped Classical
attribute [local irreducible] BinaryNat.normalize

noncomputable def fallback (d : ℕ) : ℤ[X] := if d = 0 then 1 else X ^ d - 1

theorem fallback_degree (d : ℕ) : (fallback d).natDegree = d := by
  by_cases hd : d = 0
  · simp only [fallback, hd, ite_true, natDegree_one]
  · rw [fallback, ite_eq_right hd]
    simpa only [Polynomial.C_1] using (natDegree_X_pow_sub_C (R := ℤ) (n := d) (r := 1))

theorem fallback_separable {L : Type*} [Field L] [CharZero L] (d : ℕ) :
    ((fallback d).map (Int.castRingHom L)).Separable := by
  by_cases hd : d = 0
  · simp only [fallback, hd, ite_true, Polynomial.map_one]
    exact separable_one
  · simp only [fallback, ite_eq_right hd, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    simpa only [Polynomial.C_1] using separable_X_pow_sub_C (1 : L) (Nat.cast_ne_zero.mpr hd) one_ne_zero

theorem fallback_coeff (d k : ℕ) : (fallback d).coeff k =
    if k = d then 1 else if k = 0 ∧ d ≠ 0 then -1 else 0 := by
  by_cases hd : d = 0 <;> by_cases hk : k = d <;> by_cases hz : k = 0 <;>
    simp_all [fallback, coeff_X_pow, coeff_one]

theorem fallback_bound (d k : ℕ) : ((fallback d).coeff k).natAbs ≤ 1 := by
  rw [fallback_coeff]
  split_ifs <;> norm_num

def valid (p : List Bool → ℤ[X]) (c : List Bool) : Prop := Nat.fromBitsLE (pairSnd c) = (p (pairFst c)).natDegree

noncomputable def checked (p : List Bool → ℤ[X]) (c : List Bool) : ℤ[X] :=
  if valid p c then p (pairFst c) else fallback (Nat.fromBitsLE (pairSnd c))

theorem checked_degree (p : List Bool → ℤ[X]) (c : List Bool) : (checked p c).natDegree = Nat.fromBitsLE (pairSnd c) := by
  by_cases h : valid p c
  · rw [checked, ite_eq_left h]
    exact h.symm
  · rw [checked, ite_eq_right h, fallback_degree]

theorem checked_packet (p : List Bool → ℤ[X]) (c : List Bool) :
    checked p (pair c (BinaryNatCode.encode (p c).natDegree)) = p c := by
  have h : valid p (pair c (BinaryNatCode.encode (p c).natDegree)) := by
    simp only [valid, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [checked, ite_eq_left h, pairFst_pair]

theorem checked_separable {L : Type*} [Field L] [CharZero L] (p : List Bool → ℤ[X])
    (hp : ∀ c, ((p c).map (Int.castRingHom L)).Separable) (c : List Bool) :
    ((checked p c).map (Int.castRingHom L)).Separable := by
  by_cases h : valid p c
  · rw [checked, ite_eq_left h]
    exact hp _
  · rw [checked, ite_eq_right h]
    exact fallback_separable _

theorem checked_bound (p : List Bool → ℤ[X]) (H : List Bool → ℕ)
    (hp : ∀ c k, ((p c).coeff k).natAbs ≤ 2 ^ H c) (c : List Bool) (k : ℕ) :
    ((checked p c).coeff k).natAbs ≤ 2 ^ H (pairFst c) := by
  by_cases h : valid p c
  · rw [checked, ite_eq_left h]
    exact hp _ _
  · rw [checked, ite_eq_right h]
    exact (fallback_bound _ _).trans Nat.one_le_two_pow

def context (q : List Bool) : List Bool := pairFst (pairFst q)
def origin (q : List Bool) : List Bool := pairFst (context q)
def declared (q : List Bool) : List Bool := pairSnd (context q)
def modulus (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairFst q)) + 1

noncomputable def coefficient (p : List Bool → ℤ[X]) (q : List Bool) : List Bool :=
  integerResidue ((p (context q)).coeff (Nat.fromBitsLE (pairSnd q))) (modulus q)

theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem origin_FP : origin ∈ FP := mem_FP_comp context_FP pairFst_mem_FP
theorem declared_FP : declared ∈ FP := mem_FP_comp context_FP pairSnd_mem_FP

def compare (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (declared (pairFst z)) = Nat.fromBitsLE (pairSnd z))

theorem compare_FP : (fun z => [compare z]) ∈ FP := by
  have hl := mem_FP_comp pairFst_mem_FP declared_FP
  have h : FPPred (fun z => Nat.fromBitsLE (declared (pairFst z)) = Nat.fromBitsLE (pairSnd z)) :=
    ((BinaryNat.le_fppred hl pairSnd_mem_FP).and (BinaryNat.le_fppred pairSnd_mem_FP hl)).of_iff
    (fun z => by simp only [Function.comp_apply]; omega)
  exact h.flag_mem_FP

theorem validDecider (p : List Bool → ℤ[X])
    (D : SpaceFunction (fun c => BinaryNatCode.encode (p c).natDegree)) :
    SpaceDecider {q | valid p (context q)} := by
  have E := (D.precompose origin origin_FP).withInput
  refine E.decider compare compare_FP ?_
  intro q
  simp only [compare, pairFst_pair, pairSnd_pair, Function.comp_apply, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, decide_eq_true_eq, valid, origin, declared]
  rfl

def oneValue (q : List Bool) : List Bool := ArithmeticBits.one (BinaryNat.succ (pairSnd (pairFst q)))
def negOneValue (q : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (pairSnd (pairFst q))) (BinaryNatCode.encode 1))
def fallbackValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = Nat.fromBitsLE (declared q) then oneValue q
  else if Nat.fromBitsLE (pairSnd q) = 0 ∧ Nat.fromBitsLE (declared q) ≠ 0 then negOneValue q else []

theorem fallbackValue_FP : fallbackValue ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have ho : oneValue ∈ FP := mem_FP_of_eq (mem_FP_comp hm ArithmeticBits.one_mem_FP) (fun _ => rfl)
  have hn : negOneValue ∈ FP := mem_FP_of_eq
    (mem_FP_comp (mem_FP_pair hm (constFn_mem_FP (BinaryNatCode.encode 1))) ArithmeticBits.negate_mem_FP) (fun _ => rfl)
  have he : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = Nat.fromBitsLE (declared q)) :=
    ((BinaryNat.le_fppred pairSnd_mem_FP declared_FP).and (BinaryNat.le_fppred declared_FP pairSnd_mem_FP)).of_iff (fun _ => by omega)
  have hz : FPPred (fun q => Nat.fromBitsLE (pairSnd q) = 0 ∧ Nat.fromBitsLE (declared q) ≠ 0) :=
    ((BinaryNat.le_fppred pairSnd_mem_FP (constFn_mem_FP [])).and
      (BinaryNat.lt_fppred (constFn_mem_FP []) declared_FP)).of_iff (fun _ => by change _ ≤ 0 ∧ 0 < _ ↔ _; omega)
  exact he.ite_mem_FP ho (hz.ite_mem_FP hn (constFn_mem_FP []))

theorem fallbackValue_eq (q : List Bool) : fallbackValue q =
    integerResidue ((fallback (Nat.fromBitsLE (declared q))).coeff (Nat.fromBitsLE (pairSnd q))) (modulus q) := by
  have hm : BinaryNat.succ (pairSnd (pairFst q)) = BinaryNatCode.encode (modulus q) := by
    simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, modulus]
  have ho : oneValue q = integerResidue 1 (modulus q) := by
    rw [oneValue, hm]
    simpa only [integerResidue, Int.cast_one] using ArithmeticBits.one_residueBits (modulus q)
  have hn : negOneValue q = integerResidue (-1) (modulus q) := by
    let : NeZero (modulus q) := ⟨by simp only [modulus]; omega⟩
    rw [negOneValue, hm]
    simpa only [integerResidue, Int.cast_neg, Int.cast_one, Nat.cast_one] using ArithmeticBits.negate_nat (modulus q) 1
  rw [fallbackValue, fallback_coeff]
  split_ifs <;> first | exact ho | exact hn | simp [integerResidue, residueBits, BinaryNatCode.encode]

theorem evaluator (p : List Bool → ℤ[X]) (E : SpaceFunction (coefficient p))
    (D : SpaceFunction (fun c => BinaryNatCode.encode (p c).natDegree)) : SpaceFunction (coefficient (checked p)) := by
  have R := SpaceFunction.branchDecider (validDecider p D)
    (E.precompose PrincipalCoefficientBits.sourceQuery PrincipalCoefficientBits.sourceQuery_mem_FP)
    (SpaceFunction.ofFP fallbackValue fallbackValue_FP)
  refine R.congr (funext fun q => ?_)
  change (if valid p (context q) then coefficient p (PrincipalCoefficientBits.sourceQuery q) else fallbackValue q) = _
  by_cases h : valid p (context q)
  · have hc : checked p (context q) = p (pairFst (context q)) := by rw [checked, ite_eq_left h]
    rw [ite_eq_left h]
    simp only [coefficient]
    rw [hc]
    simp only [PrincipalCoefficientBits.sourceQuery, context, modulus, pairFst_pair, pairSnd_pair]
  · have hc : checked p (context q) = fallback (Nat.fromBitsLE (pairSnd (context q))) := by
      rw [checked, ite_eq_right h]
    rw [ite_eq_right h, fallbackValue_eq]
    simp only [coefficient]
    rw [hc]
    rfl

end LeanCanny.Algebra.ValidatedDegreeBits
