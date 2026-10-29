/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceRowCoefficientCorrect

/-! # Derived-width native coefficients for the complete flat source

The exponent width is derived from the original-source degree allowance.
Every indexed row of an input-dependent-depth tower is read natively, with
the actual space-computed direction and no coefficient oracle. Invalid rows
return zero. The packet includes arbitrary monomial ranks and modulus one.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs count degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def width (F : Inputs) (u : List Bool) : ℕ := (degree F u).size
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (FlatFullSourceTower.degree_binary h).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)
theorem degree_lt_width (F : Inputs) (u : List Bool) : degree F u < 2 ^ width F u := Nat.lt_size_self _

noncomputable def value (F : Inputs) : List Bool → List Bool := FlatFullSourceRowCoefficient.value F (width F)
theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) :=
  FlatFullSourceRowCoefficient.evaluator h (width_unary h)

theorem invalid (F : Inputs) (q : List Bool) (h : ¬ FlatFullSourceRowQuery.Valid F q) : value F q = [] :=
  FlatFullSourceRowCoefficient.invalid F (width F) q h

theorem packet (F : Inputs) (u : List Bool) (i : Fin (count F u)) (r m : ℕ) :
    value F (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
      MatrixPower.residueBits (((FlatFullSourceTower.system F u i).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F u))) (width F u) r) : ℤ) : ZMod (m + 1)) := by
  generalize hq : pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m) = q
  have hu : FlatFullSourceRowQuery.source q = u := by
    rw [FlatFullSourceRowQuery.source, ← hq, pairFst_pair, pairFst_pair]
  have hi : FlatFullSourceRowQuery.rawRow q = i.val := by
    rw [FlatFullSourceRowQuery.rawRow, FlatFullSourceRowQuery.rowWord, ← hq, pairFst_pair, pairSnd_pair,
      pairFst_pair, MacaulayBits.fromBits_encode]
  have ht : Nat.fromBitsLE (FlatFullSourceRowQuery.target q) = r := by
    rw [FlatFullSourceRowQuery.target, ← hq, pairFst_pair, pairSnd_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  have hm : Nat.fromBitsLE (FlatFullSourceRowQuery.modulus q) = m := by
    rw [FlatFullSourceRowQuery.modulus, ← hq, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst u
  have H := FlatFullSourceRowCoefficient.value_at_row F (width F) q i hi (degree_lt_width F _)
  subst r
  subst m
  exact H

end LeanCanny.Encoding.FlatFullSourceCoefficient
