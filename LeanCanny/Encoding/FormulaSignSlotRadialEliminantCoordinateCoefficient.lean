/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientSpace
/-! # The actual target-coordinate row has a native FP coefficient reader -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem option_none {σ : Type*} [Fintype σ] (e : σ →₀ ℕ) (h D : ℕ) :
    e.optionElim h = Finsupp.single none D ↔ h = D ∧ e = 0 := by
  constructor
  · intro H
    constructor
    · simpa only [Finsupp.optionElim_apply_none, Finsupp.single_eq_same] using
        congrArg (fun f : Option σ →₀ ℕ => f none) H
    · ext i
      simpa only [Finsupp.optionElim_apply_some, Finsupp.single_apply, reduceCtorEq, ite_false, Finsupp.zero_apply] using
        congrArg (fun f : Option σ →₀ ℕ => f (some i)) H
  · rintro ⟨rfl, rfl⟩
    ext i
    cases i <;> simp

private theorem none_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W) (target head : List Bool → List Bool)
    (ht : target ∈ FP) (hh : head ∈ FP) :
    FPPred (fun q => homogeneousExponent read W target head q = Finsupp.single none 1) := by
  have H := ((BinaryFn.fromBits hh).eq (BinaryFn.const 1)).and (spatial_zero_FP read hr W hW target ht)
  apply H.of_iff
  intro q
  simp only [homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
    Finsupp.some_optionElim, option_none]

noncomputable def coordinateInteger (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head epsilon targetParameter : List Bool → List Bool)
    (i : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) (q : List Bool) : ℤ :=
  (if Nat.fromBitsLE (epsilon q) = 0 ∧ Nat.fromBitsLE (targetParameter q) = 1 ∧
      homogeneousExponent read W target head q = Finsupp.single none 1
    then (if FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q) = 0 ∧
      FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q) = 0 then 1 else 0)
    else 0) -
  (if Nat.fromBitsLE (epsilon q) = 0 ∧ Nat.fromBitsLE (targetParameter q) = 0 ∧
      homogeneousExponent read W target head q = Finsupp.single (some (i q)) 1
    then (if FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q) = 0 ∧
      FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q) = 0 then 1 else 0)
    else 0)

noncomputable def coordinateValue (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (i : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) :=
  residue modulus (coordinateInteger read W target head epsilon targetParameter i)

private theorem conditional_residue {m : ℕ} (P : Prop) [Decidable P] (a : ZMod m) :
    (if P then residueBits a else []) = residueBits (if P then a else 0) := by
  by_cases h : P <;> simp [h, residueBits, BinaryNatCode.encode]

theorem coordinate_value_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W)
    (target head epsilon targetParameter modulus : List Bool → List Bool)
    (ht : target ∈ FP) (hh : head ∈ FP) (he : epsilon ∈ FP) (hT : targetParameter ∈ FP) (hm : modulus ∈ FP)
    (i : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q)))
    (hi : UnaryFn (fun q => (i q).val)) :
    coordinateValue read W target head epsilon targetParameter modulus i ∈ FP := by
  have HP := parameters_zero_FP read hr W hW target ht
  have HA := ((BinaryFn.fromBits he).eq (BinaryFn.const 0)).and
    (((BinaryFn.fromBits hT).eq (BinaryFn.const 1)).and (none_FP read hr W hW target head ht hh))
  have HM := monomial_FP read hr W hW target head ht hh (fun _ => 1) (BinaryFn.const 1) i hi
  have HB := ((BinaryFn.fromBits he).eq (BinaryFn.const 0)).and
    (((BinaryFn.fromBits hT).eq (BinaryFn.const 0)).and (HM.of_iff (fun _ => eq_comm)))
  have HMod : BinaryFn (fun q => Nat.fromBitsLE (modulus q) + 1) := (BinaryFn.fromBits hm).add (BinaryFn.const 1)
  have HO := ModularScalarFP.natCast HMod (fun _ => 1) (BinaryFn.const 1)
  have EO := HP.ite_mem_FP HO (constFn_mem_FP [])
  have EA := HA.ite_mem_FP EO (constFn_mem_FP [])
  have EB := HB.ite_mem_FP EO (constFn_mem_FP [])
  have EN := mem_FP_comp (mem_FP_pair HMod.bits_mem_FP EB) ArithmeticBits.negate_mem_FP
  have HC := mem_FP_comp (mem_FP_pair HMod.bits_mem_FP (mem_FP_pair EA EN)) ArithmeticBits.addMod_mem_FP
  apply mem_FP_of_eq HC
  intro q
  simp only [Function.comp_apply, conditional_residue]
  rw [ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  by_cases hp : FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q) = 0 ∧
      FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q) = 0 <;>
    by_cases ha : Nat.fromBitsLE (epsilon q) = 0 ∧ Nat.fromBitsLE (targetParameter q) = 1 ∧
      homogeneousExponent read W target head q = Finsupp.single none 1 <;>
    by_cases hb : Nat.fromBitsLE (epsilon q) = 0 ∧ Nat.fromBitsLE (targetParameter q) = 0 ∧
      homogeneousExponent read W target head q = Finsupp.single (some (i q)) 1 <;>
    simp [coordinateValue, residue, coordinateInteger, hp, ha, hb, sub_eq_add_neg]

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
