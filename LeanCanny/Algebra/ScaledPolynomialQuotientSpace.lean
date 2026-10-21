/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ScaledPolynomialQuotient
public import LeanCanny.Algebra.CoefficientFormSpace

/-! # Native coefficients of division-free scaled quotients

Each entry in a selected Cramer determinant is one dividend coefficient, one
divisor coefficient, or zero. Binary degree controls and space-bounded original
coefficient readers suffice. Formal divisor degrees are retained modulo every
positive modulus, including when leading coefficients vanish.
-/

@[expose] public section

namespace LeanCanny.Algebra.ScaledQuotientBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open PrincipalCoefficientBits (integerResidue minimum)
attribute [local irreducible] BinaryNat.add BinaryNat.sub BinaryNat.normalize

def context (q : List Bool) : List Bool := pairFst (pairFst q)
def modulusWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def modulus (q : List Bool) : ℕ := Nat.fromBitsLE (modulusWord q) + 1
def row (p : List Bool) : List Bool := pairFst (pairSnd p)
def col (p : List Bool) : List Bool := pairSnd (pairSnd p)
def origin (p : List Bool) : List Bool := context (pairFst p)

theorem context_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulusWord_FP : modulusWord ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_FP : col ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP context_FP

structure Family where
  divisor : List Bool → ℤ[X]
  dividend : List Bool → ℤ[X]
  divisorDegree : List Bool → ℕ
  quotientDegree : List Bool → ℕ

def selected (F : Family) (q : List Bool) : Fin (F.quotientDegree (context q) + 1) :=
  ⟨min (Nat.fromBitsLE (pairSnd q)) (F.quotientDegree (context q)), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

noncomputable def family (F : Family) : Berkowitz.ModularFamily where
  dimension q := F.quotientDegree (context q) + 1
  modulus := modulus
  matrix q := ((ScaledPolynomialQuotient.matrix (F.divisor (context q)) (F.divisorDegree (context q))
    (F.quotientDegree (context q))).updateCol (selected F q)
      (ScaledPolynomialQuotient.input (F.dividend (context q)) (F.divisorDegree (context q)) (F.quotientDegree (context q)))).map
        (Int.castRingHom (ZMod (modulus q)))
  modulus_ne_zero q := by simp only [modulus]; omega

structure Access (F : Family) where
  divisorDegree : List Bool → List Bool
  quotientDegree : List Bool → List Bool
  divisorCoefficient : List Bool → List Bool
  dividendCoefficient : List Bool → List Bool
  divisorDegree_eq : ∀ c, divisorDegree c = BinaryNatCode.encode (F.divisorDegree c)
  quotientDegree_eq : ∀ c, quotientDegree c = BinaryNatCode.encode (F.quotientDegree c)
  divisor_eq : ∀ q k, divisorCoefficient (pair q (BinaryNatCode.encode k)) =
    integerResidue ((F.divisor (pairFst q)).coeff k) (Nat.fromBitsLE (pairSnd q) + 1)
  dividend_eq : ∀ q k, dividendCoefficient (pair q (BinaryNatCode.encode k)) =
    integerResidue ((F.dividend (pairFst q)).coeff k) (Nat.fromBitsLE (pairSnd q) + 1)

structure Access.ControlsPolyTime {F : Family} (a : Access F) : Prop where
  divisorDegree : a.divisorDegree ∈ FP
  quotientDegree : a.quotientDegree ∈ FP

namespace Access

def selectedCode {F : Family} (a : Access F) (q : List Bool) : List Bool :=
  minimum (pairSnd q) (a.quotientDegree (context q))
def sumIndex {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  BinaryNat.add (pair (a.divisorDegree (origin p)) (row p))
def sourceQuery (p k : List Bool) : List Bool :=
  pair (pair (origin p) (modulusWord (pairFst p))) k
def divisorQuery {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  sourceQuery p (BinaryNat.sub (pair (sumIndex a p) (col p)))
def dividendQuery {F : Family} (a : Access F) (p : List Bool) : List Bool := sourceQuery p (sumIndex a p)
def isSelected {F : Family} (a : Access F) (p : List Bool) : Prop :=
  BinaryNat.normalize (col p) = selectedCode a (pairFst p)
instance {F : Family} (a : Access F) (p : List Bool) : Decidable (isSelected a p) := inferInstanceAs (Decidable (_ = _))
def band {F : Family} (a : Access F) (p : List Bool) : Prop := Nat.fromBitsLE (col p) ≤ Nat.fromBitsLE (sumIndex a p)
instance {F : Family} (a : Access F) (p : List Bool) : Decidable (band a p) := inferInstanceAs (Decidable (_ ≤ _))
def entry {F : Family} (a : Access F) (p : List Bool) : List Bool :=
  if isSelected a p then a.dividendCoefficient (dividendQuery a p)
  else if band a p then a.divisorCoefficient (divisorQuery a p) else []

theorem selectedCode_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : selectedCode a ∈ FP :=
  PrincipalCoefficientBits.minimum_mem_FP pairSnd_mem_FP (mem_FP_comp context_FP ha.quotientDegree)
theorem sumIndex_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : sumIndex a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp origin_FP ha.divisorDegree) row_FP) BinaryNat.add_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)
theorem sourceQuery_FP {k : List Bool → List Bool} (hk : k ∈ FP) : (fun p => sourceQuery p (k p)) ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulusWord_FP
  have h := mem_FP_pair (mem_FP_pair origin_FP hm) hk
  exact mem_FP_of_eq h (fun _ => rfl)
theorem divisorQuery_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : divisorQuery a ∈ FP :=
  sourceQuery_FP (mem_FP_comp (mem_FP_pair (sumIndex_FP a ha) col_FP) BinaryNat.sub_mem_FP)
theorem dividendQuery_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : dividendQuery a ∈ FP :=
  sourceQuery_FP (sumIndex_FP a ha)
theorem selected_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : FPPred (isSelected a) :=
  stringEq_fppred (mem_FP_comp col_FP BinaryNat.normalize_mem_FP) (mem_FP_comp pairFst_mem_FP (selectedCode_FP a ha))
theorem band_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : FPPred (band a) :=
  BinaryNat.le_fppred col_FP (sumIndex_FP a ha)

theorem entryEvaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.divisorCoefficient) (Q : SpaceFunction a.dividendCoefficient) : SpaceFunction (entry a) := by
  have E := SpaceFunction.branch (fun p => decide (isSelected a p)) (selected_FP a ha).flag_mem_FP
    (Q.precompose (dividendQuery a) (dividendQuery_FP a ha))
    (SpaceFunction.branch (fun p => decide (band a p)) (band_FP a ha).flag_mem_FP
      (P.precompose (divisorQuery a) (divisorQuery_FP a ha)) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])))
  exact E.congr (funext fun p => by simp only [entry, decide_eq_true_eq, Function.comp_apply])

theorem selectedCode_eq {F : Family} (a : Access F) (q : List Bool) :
    selectedCode a q = BinaryNatCode.encode (selected F q).val := by
  simp only [selectedCode, PrincipalCoefficientBits.minimum_eq, a.quotientDegree_eq,
    selected, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem entry_packet {F : Family} (a : Access F) (q : List Bool) (i j : Fin (F.quotientDegree (context q) + 1)) :
    entry a (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((family F).matrix q i j) := by
  let p := pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hs : sumIndex a p = BinaryNatCode.encode (F.divisorDegree (context q) + i.val) := by
    simp only [p, sumIndex, origin, row, pairFst_pair, pairSnd_pair, a.divisorDegree_eq,
      BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hsel : isSelected a p ↔ j = selected F q := by
    simp only [isSelected, p, col, pairFst_pair, pairSnd_pair, selectedCode_eq,
      BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    constructor
    · intro h
      apply Fin.ext
      simpa only [Nat.fromBitsLE_bits] using congrArg Nat.fromBitsLE h
    · intro h
      exact congrArg (fun z : Fin (F.quotientDegree (context q) + 1) => z.val.bits) h
  have hb : band a p ↔ j.val ≤ F.divisorDegree (context q) + i.val := by
    dsimp only [band]
    rw [hs]
    simp only [p, col, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hP := a.divisor_eq (pair (context q) (modulusWord q)) (F.divisorDegree (context q) + i.val - j.val)
  have hQ := a.dividend_eq (pair (context q) (modulusWord q)) (F.divisorDegree (context q) + i.val)
  rw [pairFst_pair, pairSnd_pair] at hP hQ
  change _ = integerResidue _ (modulus q) at hP hQ
  have hqp : divisorQuery a p = pair (pair (context q) (modulusWord q))
      (BinaryNatCode.encode (F.divisorDegree (context q) + i.val - j.val)) := by
    rw [divisorQuery, hs]
    simp only [sourceQuery, p, origin, col, pairFst_pair, pairSnd_pair,
      BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hqq : dividendQuery a p = pair (pair (context q) (modulusWord q))
      (BinaryNatCode.encode (F.divisorDegree (context q) + i.val)) := by
    rw [dividendQuery, hs]
    simp only [sourceQuery, p, origin, pairFst_pair]
  have hc := congrArg (fun z : ℤ => integerResidue z (modulus q))
    (ScaledPolynomialQuotient.selected_entry (F.divisor (context q)) (F.dividend (context q))
      (F.divisorDegree (context q)) (F.quotientDegree (context q)) (selected F q) i j)
  change entry a p = integerResidue _ (modulus q)
  refine Eq.trans ?_ hc.symm
  simp only [entry, hsel, hb]
  by_cases hj : j = selected F q
  · rw [ite_eq_left hj, ite_eq_left hj]
    rw [hqq]
    exact hQ
  · rw [ite_eq_right hj, ite_eq_right hj]
    by_cases hg : j.val ≤ F.divisorDegree (context q) + i.val
    · rw [ite_eq_left hg, ite_eq_left hg]
      rw [hqp]
      exact hP
    · rw [ite_eq_right hg, ite_eq_right hg]
      simp only [integerResidue, residueBits, Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
      rfl

noncomputable def modular {F : Family} (a : Access F) : Berkowitz.ModularAccess (family F) where
  access := ⟨BinaryNat.succ ∘ a.quotientDegree ∘ context, BinaryNat.succ ∘ modulusWord, entry a⟩
  correct q := {
    dimension := by simp only [Function.comp_apply, a.quotientDegree_eq, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, family]
    modulus := by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, BinaryNatCode.encode, family, modulus]
    entry := entry_packet a q }

theorem modular_controls {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : a.modular.ControlsPolyTime := by
  have hd := mem_FP_comp (mem_FP_comp context_FP ha.quotientDegree) BinaryNat.succ_mem_FP
  have hm := mem_FP_comp modulusWord_FP BinaryNat.succ_mem_FP
  constructor
  · simpa only [modular] using hd
  · simpa only [modular] using hm

noncomputable def value (F : Family) (q : List Bool) : List Bool :=
  integerResidue ((ScaledPolynomialQuotient.quotient (F.divisor (context q)) (F.dividend (context q))
    (F.divisorDegree (context q)) (F.quotientDegree (context q))).coeff (Nat.fromBitsLE (pairSnd q))) (modulus q)

theorem determinant_value (F : Family) (q : List Bool) : (family F).value q =
    integerResidue (((ScaledPolynomialQuotient.matrix (F.divisor (context q)) (F.divisorDegree (context q))
      (F.quotientDegree (context q))).updateCol (selected F q)
        (ScaledPolynomialQuotient.input (F.dividend (context q)) (F.divisorDegree (context q))
          (F.quotientDegree (context q)))).det) (modulus q) := by
  let M := (ScaledPolynomialQuotient.matrix (F.divisor (context q)) (F.divisorDegree (context q))
    (F.quotientDegree (context q))).updateCol (selected F q)
      (ScaledPolynomialQuotient.input (F.dividend (context q)) (F.divisorDegree (context q)) (F.quotientDegree (context q)))
  change residueBits (M.map (Int.castRingHom (ZMod (modulus q)))).det = integerResidue M.det (modulus q)
  exact congrArg residueBits ((Int.castRingHom (ZMod (modulus q))).map_det M).symm

def within {F : Family} (a : Access F) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd q) ≤ Nat.fromBitsLE (a.quotientDegree (context q))
instance {F : Family} (a : Access F) (q : List Bool) : Decidable (within a q) := inferInstanceAs (Decidable (_ ≤ _))

theorem within_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : FPPred (within a) :=
  BinaryNat.le_fppred pairSnd_mem_FP (mem_FP_comp context_FP ha.quotientDegree)

theorem evaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.divisorCoefficient) (Q : SpaceFunction a.dividendCoefficient) : SpaceFunction (value F) := by
  have E := Berkowitz.ModularAccess.evaluator a.modular (modular_controls a ha) (entryEvaluator a ha P Q)
  have R := SpaceFunction.branch (fun q => decide (within a q)) (within_FP a ha).flag_mem_FP E
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  have hw : within a q ↔ Nat.fromBitsLE (pairSnd q) ≤ F.quotientDegree (context q) := by
    simp only [within, a.quotientDegree_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [decide_eq_true_eq, hw]
  rw [value, ScaledPolynomialQuotient.quotient_coeff]
  by_cases hk : Nat.fromBitsLE (pairSnd q) < F.quotientDegree (context q) + 1
  · rw [ite_eq_left (by omega), dite_eq_left hk, determinant_value]
    have hs : selected F q = ⟨Nat.fromBitsLE (pairSnd q), hk⟩ := Fin.ext (Nat.min_eq_left (by omega))
    rw [hs]
  · rw [ite_eq_right (by omega), dite_eq_right hk]
    simp only [integerResidue, residueBits, Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
    rfl

end Access
end LeanCanny.Algebra.ScaledQuotientBits
