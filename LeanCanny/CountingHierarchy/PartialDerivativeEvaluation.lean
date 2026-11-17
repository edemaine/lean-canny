/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PartialDerivativeAddresses
public import LeanCanny.CountingHierarchy.TranslatedCoefficientEvaluation

/-! # First and mixed second derivatives at one additional counting level -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped Classical

@[expose] noncomputable def firstPartialResidue (p n i : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  translatedCoefficientResidue p n (firstPartialAddress n i) z value

@[expose] noncomputable def secondPartialResidue (p n i j : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  (translatedCoefficientResidue p n (secondPartialAddress n i j) z value *
    (if i = j then 2 else 1)) % p

theorem firstPartialResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n i : α → ℕ} {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => firstPartialResidue (p w) (n w) (i w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat :=
  translatedCoefficientResidue_mem E hp hn (firstPartialAddress_polyTime hn hi) hz hv

theorem secondPartialResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n i j : α → ℕ} {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => secondPartialResidue (p w) (n w) (i w) (j w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hcoeff := translatedCoefficientResidue_mem E hp hn (secondPartialAddress_polyTime hn hi hj) hz hv
  have htest : ComputableInPolyTime (fun w => decide (i w = j w)) enc encBool := by fun_prop
  have hfactor : ComputableInPolyTime (fun w => if i w = j w then 2 else 1) enc encNat := by
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (.const (2 : ℕ)) (.const 1)
  simpa only [secondPartialResidue, decide_eq_true_eq] using
    CountingFunction.nat_mod (CountingFunction.nat_mul hcoeff (CountingFunction.of_polyTime hfactor))
      (CountingFunction.of_polyTime hp)

theorem firstPartialResidue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (i : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun j : Fin n => ((y[j.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (firstPartialResidue p n i.val z value : ZMod p) =
      eval (fun j : Fin n => ((z[j.val]?.getD 0 : ℕ) : ZMod p)) (pderiv i F) := by
  rw [firstPartialResidue, translatedCoefficientResidue_cast F (Finsupp.single i 1)
    (firstPartialAddress n i.val) z value hF (by
      intro j
      simp only [Finsupp.single_apply]
      split_ifs <;> omega) (by
      intro j
      rw [firstPartialAddress_get _ j.isLt]
      simp only [Finsupp.single_apply, Fin.val_inj, eq_comm]) hv]
  exact (first_derivative_translation_coeff _ F i).symm

theorem secondPartialResidue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (i j : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun k : Fin n => ((y[k.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (secondPartialResidue p n i.val j.val z value : ZMod p) =
      eval (fun k : Fin n => ((z[k.val]?.getD 0 : ℕ) : ZMod p)) (pderiv j (pderiv i F)) := by
  rw [secondPartialResidue, ZMod.natCast_mod, Nat.cast_mul,
    translatedCoefficientResidue_cast F (Finsupp.single j 1 + Finsupp.single i 1)
      (secondPartialAddress n i.val j.val) z value hF (by
        intro k
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs <;> omega) (by
        intro k
        rw [secondPartialAddress_get _ _ k.isLt]
        simp only [Finsupp.add_apply, Finsupp.single_apply, Fin.val_inj, eq_comm]) hv,
    second_derivative_translation_coeff]
  congr 1
  by_cases hij : i = j
  · subst j
    simp
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [hij, hval]

end LeanCanny.CountingHierarchy
