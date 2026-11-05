/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientQuery
public import LeanCanny.Algebra.FixedWidthPowerMonomial
public import LeanCanny.Computation.PolyTimeBinaryRange
/-! # Native guards for a literal formal tilted-system coefficient query -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceExponent (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (q : List Bool) :=
  FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialFormalInput.dimension (read q))))
    (W q) (Nat.fromBitsLE (target q))
noncomputable def homogeneousExponent (read : List Bool → List Bool) (W : List Bool → ℕ)
    (target head : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous (read q) (sourceExponent read W target q)
    (Nat.fromBitsLE (head q))

private theorem prefix_native {m a : ℕ} (W r : ℕ) :
    (Finsupp.equivFunOnFinite.symm (fun i : Fin m =>
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (m + (a + 1)))) W r (Fin.castAdd (a + 1) i)) : Fin m →₀ ℕ) =
        FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin m)) W r := by
  ext i
  rfl

theorem spatial_native (c : List Bool) (W r : ℕ) :
    FormulaSignSlotRadialEliminantCoefficientQuery.spatial c
      (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialFormalInput.dimension c))) W r) =
        FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialFormalInput.spatial c))) W r :=
  prefix_native W r

private theorem coordinate_binary (W : List Bool → ℕ) (target : List Bool → List Bool)
    (hW : UnaryFn W) (ht : target ∈ FP) :
    BinaryFn (fun z => FixedWidthQuery.coordinate W target (pairFst z) (pairSnd z).length) :=
  BinaryFn.fromBits (take_mem_FP
    (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hW.lift)) hW.lift)

private theorem tail_zero (A S W : List Bool → ℕ) (target : List Bool → List Bool)
    (hA : UnaryFn A) (hS : UnaryFn S) (hW : UnaryFn W) (ht : target ∈ FP) :
    FPPred (fun q => ∀ i : Fin (A q), S q ≤ i.val →
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A q))) (W q) (Nat.fromBitsLE (target q)) i = 0) := by
  have H := FPPred.forall_lt hA
    (((BinaryFn.ofUnary UnaryFn.index).lt (BinaryFn.ofUnary hS.lift)).or
      ((coordinate_binary W target hW ht).eq (BinaryFn.const 0)))
  apply H.of_iff
  intro q
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  constructor
  · intro H i hi
    have HE := H i.val i.isLt
    rw [FixedWidthPowerMonomial.native_coordinate A W target q i]
    omega
  · intro H i hi
    by_cases h : i < S q
    · exact Or.inl h
    · exact Or.inr (by
        have HE := H ⟨i, hi⟩ (by change S q ≤ i; omega)
        simpa only [FixedWidthPowerMonomial.native_coordinate] using HE)

theorem parameters_zero_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W) (target : List Bool → List Bool) (ht : target ∈ FP) :
    FPPred (fun q => FormulaSignSlotRadialEliminantCoefficientQuery.radius (read q) (sourceExponent read W target q) = 0 ∧
      FormulaSignSlotRadialEliminantCoefficientQuery.center (read q) (sourceExponent read W target q) = 0) := by
  apply (tail_zero (FormulaSignSlotRadialFormalInput.dimension ∘ read)
    (FormulaSignSlotRadialFormalInput.spatial ∘ read) W target
    (FormulaSignSlotRadialFormalInput.dimension_unary.comp hr)
    (FormulaSignSlotRadialFormalInput.spatial_unary.comp hr) hW ht).of_iff
  intro q
  exact (FormulaSignSlotRadialEliminantCoefficientQuery.parameters_zero (read q) _).symm

theorem spatial_zero_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W) (target : List Bool → List Bool) (ht : target ∈ FP) :
    FPPred (fun q => (homogeneousExponent read W target (fun _ => []) q).some = 0) := by
  apply (FixedWidthQuery.bounded_fppred (FormulaSignSlotRadialFormalInput.spatial_unary.comp hr)
    hW (UnaryFn.const 0) ht).of_iff
  intro q
  change (∀ i < FormulaSignSlotRadialFormalInput.spatial (read q),
    FixedWidthQuery.coordinate W target q i ≤ 0) ↔ _
  rw [homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
    Finsupp.some_optionElim, sourceExponent, spatial_native]
  constructor
  · intro H
    ext i
    rw [FixedWidthPowerMonomial.native_coordinate (fun q => FormulaSignSlotRadialFormalInput.spatial (read q)) W target q i]
    exact Nat.eq_zero_of_le_zero (H i.val i.isLt)
  · intro H i hi
    have HE := congrArg (fun e : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)) →₀ ℕ => e ⟨i, hi⟩) H
    have HC := FixedWidthPowerMonomial.native_coordinate (fun q => FormulaSignSlotRadialFormalInput.spatial (read q)) W target q ⟨i, hi⟩
    exact (HC.symm.trans HE).le

theorem homogeneous_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W) (target head : List Bool → List Bool)
    (ht : target ∈ FP) (hh : head ∈ FP) :
    FPPred (fun q => Finsupp.weight (WeightedHomogenization.weights (fun _ : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)) => 1))
      (homogeneousExponent read W target head q) = 2 * degreeBudget (read q) + 1) := by
  have HS := BinaryFn.sum (FormulaSignSlotRadialFormalInput.spatial_unary.comp hr) (coordinate_binary W target hW ht)
  have H := ((BinaryFn.fromBits hh).add HS).eq
    (BinaryFn.ofUnary (((UnaryFn.const 2).mul (degreeBudget_unary.comp hr)).add (UnaryFn.const 1)))
  apply H.of_iff
  intro q
  simp only [pairFst_pair, pairSnd_pair, List.length_replicate]
  rw [homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
    WeightedHomogenization.weight_split, Finsupp.optionElim_apply_none, Finsupp.some_optionElim,
    sourceExponent, spatial_native, Finsupp.weight_eq_sum]
  simp only [smul_eq_mul, mul_one]
  have HC : (∑ i : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)),
      FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W q) (Nat.fromBitsLE (target q)) i) =
        ∑ i ∈ Finset.range (FormulaSignSlotRadialFormalInput.spatial (read q)), FixedWidthQuery.coordinate W target q i := by
    calc
      _ = ∑ i : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)), FixedWidthQuery.coordinate W target q i.val := by
        apply Finset.sum_congr rfl
        intro i _
        exact FixedWidthPowerMonomial.native_coordinate (fun q => FormulaSignSlotRadialFormalInput.spatial (read q)) W target q i
      _ = _ := Fin.sum_univ_eq_sum_range _ _
  rw [HC]

theorem monomial_FP (read : List Bool → List Bool) (hr : read ∈ FP)
    (W : List Bool → ℕ) (hW : UnaryFn W) (target head : List Bool → List Bool)
    (ht : target ∈ FP) (hh : head ∈ FP) (D : List Bool → ℕ) (hD : BinaryFn D)
    (j : (q : List Bool) → Fin (FormulaSignSlotRadialFormalInput.spatial (read q)))
    (hj : UnaryFn (fun q => (j q).val)) :
    FPPred (fun q => Finsupp.single (some (j q)) (D q) = homogeneousExponent read W target head q) := by
  have H := ((BinaryFn.fromBits hh).eq (BinaryFn.const 0)).and
    (FixedWidthPowerMonomial.matches_FP (FormulaSignSlotRadialFormalInput.spatial ∘ read) W D
      (fun q => (j q).val) target (FormulaSignSlotRadialFormalInput.spatial_unary.comp hr) hW hD
        (BinaryFn.ofUnary hj) ht)
  apply H.of_iff
  intro q
  rw [FixedWidthPowerMonomial.matches_iff _ _ _ _ _ q (j q).isLt]
  change Nat.fromBitsLE (head q) = 0 ∧
    FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FormulaSignSlotRadialFormalInput.spatial (read q)))) (W q) (Nat.fromBitsLE (target q)) = Finsupp.single (j q) (D q) ↔ _
  rw [homogeneousExponent, FormulaSignSlotRadialEliminantCoefficientQuery.homogeneous,
    sourceExponent, spatial_native]
  constructor
  · rintro ⟨HH, HS⟩
    ext i
    cases i with
    | none => simp [HH]
    | some i => simpa only [Finsupp.single_apply, Option.some.injEq, Finsupp.optionElim_apply_some] using
        (congrArg (fun e : Fin (FormulaSignSlotRadialFormalInput.spatial (read q)) →₀ ℕ => e i) HS).symm
  · intro H
    constructor
    · simpa only [Finsupp.single_apply, reduceCtorEq, ite_false, Finsupp.optionElim_apply_none] using
        (congrArg (fun e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) →₀ ℕ => e none) H).symm
    · ext i
      simpa only [Finsupp.single_apply, Option.some.injEq, Finsupp.optionElim_apply_some] using
        (congrArg (fun e : Option (Fin (FormulaSignSlotRadialFormalInput.spatial (read q))) →₀ ℕ => e (some i)) H).symm

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantCoefficientNative
