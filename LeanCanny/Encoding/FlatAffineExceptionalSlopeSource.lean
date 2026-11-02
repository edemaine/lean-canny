/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalOrderedRule
public import LeanCanny.Encoding.FlatAffineExceptionalBankDenominator
/-! # The actual exceptional sweep slope uses only original integer source access -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSlopeSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births)
open scoped Classical BigOperators

noncomputable def height (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :=
  FlatAffineExceptionalBankSource.massBound F C h u * births F u + 1

theorem denominator_bound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    (FlatAffineExceptionalBankSource.denominator F C h u).natAbs ≤
      2 ^ (FlatAffineExceptionalBankSource.massBound F C h u * births F u) := by
  have HP (i : Fin (births F u)) :
      (FlatAffineExceptionalBankSource.finitePolynomial F C h u i).leadingCoeff.natAbs ≤
        2 ^ FlatAffineExceptionalBankSource.massBound F C h u := by
    have HM := FlatAffineExceptionalBankSource.mass_le F C h (pair u (BinaryNatCode.encode i.val))
    rw [pairFst_pair] at HM
    exact (coeff_natAbs_le_coefficientMass _ _).trans HM
  have H := CommonIntegerDenominator.denominator_abs_bound (Finset.univ : Finset (Fin (births F u)))
    (fun i => (FlatAffineExceptionalBankSource.finitePolynomial F C h u i).leadingCoeff)
    (2 ^ FlatAffineExceptionalBankSource.massBound F C h u) (fun i _ => HP i)
  simpa only [CommonIntegerDenominator.denominator, FlatAffineExceptionalBankSource.denominator,
    Finset.card_univ, Fintype.card_fin, ← pow_mul] using H

theorem denominator_size (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    (FlatAffineExceptionalBankSource.denominator F C h u).natAbs.size ≤ height F C h u := by
  apply Nat.size_le.mpr
  exact (denominator_bound F C h u).trans_lt (by
    unfold height
    rw [pow_succ]
    have H := Nat.two_pow_pos (FlatAffineExceptionalBankSource.massBound F C h u * births F u)
    omega)

theorem height_binary {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : BinaryFn (height F C h) :=
  ((FlatAffineExceptionalBankSource.massBound_binary hF C h hh).mul
    (BinaryFn.ofUnary (FlatAffineExceptionalBankSource.births_unary hF))).add (BinaryFn.const 1)

theorem slope_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ FlatAffineExceptionalOrderedRule.frozen F u) (r : Fin (arity F u))
    (hr : r ∉ FlatAffineExceptionalOrderedRule.frozen F u) :
    (FlatAffineExceptionalOrderedRule.sweep F C h S u hm hh r hr).slope =
      FlatAffineExceptionalBankSource.denominator F C h u :=
  FlatAffineExceptionalBankSource.denominator_bank F C h S u (hm.trans (Nat.le_succ S))

theorem slope_evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (S : List Bool → ℕ) (hm : ∀ q, births F (pairFst q) ≤ S q)
    (hf : ∀ q, h (pairFst q) ∈ FlatAffineExceptionalOrderedRule.frozen F (pairFst q))
    (r : (q : List Bool) → Fin (arity F (pairFst q)))
    (hr : ∀ q, r q ∉ FlatAffineExceptionalOrderedRule.frozen F (pairFst q)) :
    SpaceFunction (fun q => residueBits
      ((FlatAffineExceptionalOrderedRule.sweep F C h (S q) (pairFst q) (hm q) (hf q) (r q) (hr q)).slope :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1))) := by
  apply (FlatAffineExceptionalBankSource.denominator_evaluator hF C h hh).congr
  funext q
  rw [slope_eq]
  rfl
end LeanCanny.Encoding.FlatAffineExceptionalSlopeSource
