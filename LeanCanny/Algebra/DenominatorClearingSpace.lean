/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteDenominatorClearing
public import LeanCanny.Algebra.ModularProductSpace
public import LeanCanny.Computation.SpaceFunctionComposition
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Encoding.BracketsFP

/-! # Streamed modular coefficients of explicit denominator clearing

A child supplies numerator and denominator residues for a finite rational
coefficient family. A modular product skips the selected denominator, then
multiplies by its numerator. Count and selected-index fields stay binary; all
child computations and retained contexts are included in the space certificate.
No inverse is taken, even at moduli dividing a rational denominator.
-/

@[expose] public section

namespace LeanCanny.Algebra.DenominatorClearing

open LeanCanny.Encoding LeanCanny.Encoding.Brackets LeanCanny.Computation
open MatrixPower
open scoped BigOperators

structure Family where
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  index : (c : List Bool) → Fin (count c)
  coefficient : (c : List Bool) → Fin (count c) → ℚ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits ((FiniteDenominatorClearing.cleared (F.coefficient c) (F.index c) : ℤ) : ZMod (F.modulus c))

noncomputable def Family.factor (F : Family) (c : List Bool) (j : ℕ) : ZMod (F.modulus c) :=
  if hj : j < F.count c then if j = (F.index c).val then 1 else ((F.coefficient c ⟨j, hj⟩).den : ZMod (F.modulus c)) else 1

theorem Family.cleared_eq_product (F : Family) (c : List Bool) :
    ((FiniteDenominatorClearing.cleared (F.coefficient c) (F.index c) : ℤ) : ZMod (F.modulus c)) =
      ((F.coefficient c (F.index c)).num : ZMod (F.modulus c)) * ∏ j ∈ Finset.range (F.count c), F.factor c j := by
  rw [FiniteDenominatorClearing.cleared_eq_product, Int.cast_mul, Int.cast_prod, Finset.prod_range]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases he : j = F.index c
  · subst j
    simp [factor]
  · have hn : j.val ≠ (F.index c).val := fun h => he (Fin.ext h)
    simp [factor, j.isLt, he, hn]

structure Access (F : Family) where
  count : List Bool → List Bool
  modulus : List Bool → List Bool
  selected : List Bool → List Bool
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  count_eq : ∀ c, count c = BinaryNatCode.encode (F.count c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  selected_eq : ∀ c, selected c = BinaryNatCode.encode (F.index c).val
  numerator_eq : ∀ c, numerator c = residueBits ((F.coefficient c (F.index c)).num : ZMod (F.modulus c))
  denominator_eq : ∀ c (j : Fin (F.count c)), denominator (pair c (BinaryNatCode.encode j.val)) =
    residueBits ((F.coefficient c j).den : ZMod (F.modulus c))

def skip (selected : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd p) = Nat.fromBitsLE (selected (pairFst p)))

def maskedFactor (selected modulus f : List Bool → List Bool) (p : List Bool) : List Bool :=
  if skip selected p then ArithmeticBits.one (modulus (pairFst p)) else f p

theorem skip_mem_FP {selected : List Bool → List Bool} (hs : selected ∈ FP) :
    (fun p => [skip selected p]) ∈ FP := by
  have ht := mem_FP_comp pairFst_mem_FP hs
  have hp := ((BinaryNat.le_fppred pairSnd_mem_FP ht).and (BinaryNat.le_fppred ht pairSnd_mem_FP)).of_iff
    (q := fun p => Nat.fromBitsLE (pairSnd p) = Nat.fromBitsLE (selected (pairFst p))) (fun p => by dsimp only [Function.comp_apply]; omega)
  exact hp.flag_mem_FP

theorem maskedFactorEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (selected modulus : List Bool → List Bool) (hs : selected ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (maskedFactor selected modulus f) := by
  have hsrc := mem_FP_comp pairFst_mem_FP hm
  have hone := mem_FP_comp hsrc ArithmeticBits.one_mem_FP
  let Q := SpaceFunction.branch (skip selected) (skip_mem_FP hs) (SpaceFunction.ofFP _ hone) E
  exact Q.congr (funext fun _ => rfl)

def finish (modulus : List Bool → List Bool) (p : List Bool) : List Bool :=
  ArithmeticBits.combine (pair (modulus (pairFst p))
    (pair [] (pair (pairFst (pairSnd p)) (pairSnd (pairSnd p)))))

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : finish modulus ∈ FP := by
  have hp := mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hm)
    (mem_FP_pair (constFn_mem_FP []) hp)) ArithmeticBits.combine_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem Access.maskedFactor_packet {F : Family} (a : Access F) (c : List Bool) (j : ℕ) (hj : j < F.count c) :
    maskedFactor a.selected a.modulus a.denominator (pair c (BinaryNatCode.encode j)) = residueBits (F.factor c j) := by
  simp only [maskedFactor, skip, pairFst_pair, pairSnd_pair, a.selected_eq,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases he : j = (F.index c).val
  · simp only [he, decide_true, ↓reduceIte, a.modulus_eq, ArithmeticBits.one_residueBits,
      Family.factor, dite_eq_left (F.index c).isLt]
  · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
    calc
      a.denominator (pair c j.bits) = residueBits ((F.coefficient c ⟨j, hj⟩).den : ZMod (F.modulus c)) := by
        simpa only [BinaryNatCode.encode] using a.denominator_eq c ⟨j, hj⟩
      _ = residueBits (F.factor c j) := by simp only [Family.factor, dite_eq_left hj, ite_eq_right he]

theorem Access.productEvaluator {F : Family} (a : Access F)
    (hc : a.count ∈ FP) (hm : a.modulus ∈ FP) (hs : a.selected ∈ FP) (D : SpaceFunction a.denominator) :
    SpaceFunction (fun c => residueBits (∏ j ∈ Finset.range (F.count c), F.factor c j)) := by
  let E := maskedFactorEvaluator D a.selected a.modulus hs hm
  have hmod : (fun c => Nat.fromBitsLE (a.modulus c)) = F.modulus := by
    funext c
    simp only [a.modulus_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hf (c : List Bool) (j : ℕ) (hj : j < Nat.fromBitsLE (a.count c)) :
      maskedFactor a.selected a.modulus a.denominator (pair c (BinaryNatCode.encode j)) = residueBits (F.factor c j) := by
    apply a.maskedFactor_packet
    simpa only [a.count_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hj
  let P := ModularProduct.evaluatorWithModulus E a.count a.modulus hc hm F.modulus hmod F.factor
    (fun c => Nat.pos_of_ne_zero (F.modulus_ne_zero c)) hf
  refine P.congr (funext fun c => ?_)
  simp only [a.count_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem finish_residues (modulus : List Bool → List Bool) (c : List Bool) (m : ℕ) [NeZero m]
    (hm : modulus c = BinaryNatCode.encode m) (x y : ZMod m) :
    finish modulus (pair c (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  have hz : residueBits (0 : ZMod m) = [] := by simp [residueBits, BinaryNatCode.encode]
  simp only [finish, pairFst_pair, pairSnd_pair, hm]
  rw [← hz, ArithmeticBits.combine_residueBits, zero_add]

theorem Access.evaluator {F : Family} (a : Access F)
    (hc : a.count ∈ FP) (hm : a.modulus ∈ FP) (hs : a.selected ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : SpaceFunction F.value := by
  let P := a.productEvaluator hc hm hs D
  let Q := (N.pairOutputs P).withInput.postcompose (finish a.modulus) (finish_mem_FP hm)
  refine Q.congr (funext fun c => ?_)
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  dsimp only [Function.comp_apply]
  rw [a.numerator_eq, finish_residues a.modulus c _ (a.modulus_eq c), ← F.cleared_eq_product]
  rfl

end LeanCanny.Algebra.DenominatorClearing
