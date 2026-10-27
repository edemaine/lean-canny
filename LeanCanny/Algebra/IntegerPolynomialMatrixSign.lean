/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialMatrixSpace
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.InfinitesimalSignSpace

/-! # Native signs of the first determinant coefficient

A binary bit budget and the original signed entry reader suffice. Modular
determinants feed CRT sign extraction without storing the full coefficient.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def firstQuery (q : List Bool) : List Bool := pair (pair (pairFst q) (BinaryNatCode.encode 1)) (pairSnd q)
theorem firstQuery_FP : firstQuery ∈ FP := mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP _)) pairSnd_mem_FP

noncomputable def firstCoefficient (F : Family) (c : List Bool) : ℤ := (F.matrix c).det.coeff 1
noncomputable def firstResidue (F : Family) : List Bool → List Bool := value F ∘ firstQuery

theorem firstResidue_evaluator (F : Family) {code : List Bool → List Bool} (E : SpaceFunction code)
    (hc : EntryCorrect F code) (hN : BinaryFn F.dimension) : SpaceFunction (firstResidue F) :=
  (evaluator F E hc hN).precompose firstQuery firstQuery_FP

theorem firstResidue_packet (F : Family) (c m : List Bool) :
    firstResidue F (pair c m) = residueBits ((firstCoefficient F c : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  rw [firstResidue, Function.comp_apply, firstQuery, pairFst_pair, pairSnd_pair, value_packet]
  rfl

attribute [local irreducible] firstCoefficient firstResidue value

theorem firstSign_evaluator (F : Family) {code : List Bool → List Bool} (E : SpaceFunction code)
    (hc : EntryCorrect F code) (hN : BinaryFn F.dimension) (budget : List Bool → ℕ) (hb : BinaryFn budget)
    (hbudget : ∀ c, (firstCoefficient F c).natAbs.size ≤ budget c) :
    SpaceFunction (fun c => InfinitesimalSign.encode (SignType.sign (firstCoefficient F c))) := by
  have R := firstResidue_evaluator F E hc hN
  have H := IntegerSignumBits.evaluator R (fun c => BinaryNatCode.encode (budget c)) hb.bits_mem_FP (firstCoefficient F)
    (by intro c; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact hbudget c)
    (by
      intro c m hm
      generalize hw : BinaryNatCode.encode (m - 1) = w
      have he : Nat.fromBitsLE w + 1 = m := by
        rw [← hw]
        simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      subst m
      exact firstResidue_packet F c w)
  exact H.congr (funext fun c => InfinitesimalSign.tag_eq_encode (firstCoefficient F c))

end LeanCanny.Algebra.IntegerPolynomialMatrixBits
