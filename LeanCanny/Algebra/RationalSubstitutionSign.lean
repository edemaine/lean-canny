/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionResidue
public import LeanCanny.Algebra.IndexedRationalSubstitutionBudget
public import LeanCanny.Algebra.InfinitesimalResidueSpace

/-!
# Certified infinitesimal signs after streamed rational substitution

FP source metadata, exponents, coordinate degree bounds, and coefficient-bit
bounds combine with suspended source/coordinate residue routines. The resulting
certificate computes the sign of the cleared numerator for a sufficiently small
positive parameter. Even denominator widths preserve the sign of the original
rational substitution wherever its coordinate denominators are nonzero.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.IntegerBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open Polynomial

noncomputable def Access.signEvaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (C : SpaceFunction a.coefficient) (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator)
    (coordinateDegree coordinateBits sourceBits : List Bool → List Bool)
    (hE : coordinateDegree ∈ FP) (hb : coordinateBits ∈ FP) (hs : sourceBits ∈ FP)
    (hsource : ∀ c r, r < F.terms c → (F.coefficient c r).natAbs ≤ 2 ^ Nat.fromBitsLE (sourceBits c))
    (hnD : ∀ c i, i < F.arity c → (F.numerator c i).natDegree ≤ Nat.fromBitsLE (coordinateDegree c))
    (hdD : ∀ c i, i < F.arity c → (F.denominator c i).natDegree ≤ Nat.fromBitsLE (coordinateDegree c))
    (hn : ∀ c i, i < F.arity c → ∀ k, ((F.numerator c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (coordinateBits c))
    (hd : ∀ c i, i < F.arity c → ∀ k, ((F.denominator c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (coordinateBits c)) :
    SpaceFunction (fun c => InfinitesimalSign.tag (F.polynomial c).trailingCoeff) := by
  let degree := fun c => Indexed.degreeCode (a.arity c) (a.width c) (coordinateDegree c)
  let budget := fun c => Indexed.coefficientBudgetCode (a.arity c) (a.width c) (a.terms c)
    (coordinateDegree c) (coordinateBits c) (sourceBits c)
  have hdegree : degree ∈ FP := Indexed.degreeCode_mem_FP ha.arity ha.width hE
  have hbudget : budget ∈ FP := Indexed.coefficientBudgetCode_mem_FP ha.arity ha.width ha.terms hE hb hs
  have hdegree_bound (c : List Bool) : (F.polynomial c).natDegree ≤ Nat.fromBitsLE (degree c) := by
    simp only [degree, Indexed.degreeCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits, a.arity_eq, a.width_eq]
    exact Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _ (F.exponent_le c) (hnD c) (hdD c)
  have hbudget_bound (q : List Bool) :
      ((F.polynomial (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))).natAbs.size ≤ Nat.fromBitsLE ((budget ∘ pairFst) q) := by
    simp only [Function.comp_apply, budget, Indexed.coefficientBudgetCode_code, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, a.arity_eq, a.width_eq, a.terms_eq]
    exact Indexed.coeff_size_cleared_le _ _ _ _ _ _ _ _ _ (F.exponent_le _) (hsource _)
      (fun i hi => coefficientMass_le_pow_of_degree_coeff _ _ _ (hnD _ i hi) (hn _ i hi))
      (fun i hi => coefficientMass_le_pow_of_degree_coeff _ _ _ (hdD _ i hi) (hd _ i hi)) _
  exact InfinitesimalSign.evaluatorOfResidues (a.evaluator ha C N D) degree (budget ∘ pairFst)
    hdegree (mem_FP_comp pairFst_mem_FP hbudget) F.polynomial hdegree_bound hbudget_bound F.value_packet

theorem Family.sign_substitution (F : Family) (c : List Bool) (D : ℕ) (hwidth : F.width c = 2 * D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ →
      (∀ i, i < F.arity c → (F.denominator c i).eval₂ (Int.castRingHom ℝ) x ≠ 0) →
      SignType.sign ((Indexed.source (F.arity c) (F.terms c) (F.coefficient c) (F.exponent c)).eval₂
        (Int.castRingHom ℝ) (fun i => (F.numerator c i.val).eval₂ (Int.castRingHom ℝ) x /
          (F.denominator c i.val).eval₂ (Int.castRingHom ℝ) x)) = SignType.sign (F.polynomial c).trailingCoeff := by
  obtain ⟨δ, hδ, hsign⟩ := InfinitesimalSign.integer_sign_eval_eq_trailingCoeff (F.polynomial c)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxd hden
  have hclear := Indexed.sign_eval₂_cleared (Int.castRingHom ℝ) x (F.arity c) (F.terms c) D
    (F.coefficient c) (F.exponent c) (F.numerator c) (F.denominator c)
    (by simpa only [← hwidth] using F.exponent_le c) hden
  rw [← hwidth] at hclear
  exact hclear.symm.trans (hsign x hx hxd)

end LeanCanny.Algebra.RationalSubstitution.IntegerBits
