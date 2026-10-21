/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionSpace

/-!
# Uniform integer coefficient residues after rational substitution

The input is `pair (pair context selectedDegree) (m-1)`. Source and coordinate
coefficient routines receive the same modulus through canonical binary words.
FP metadata and exponent readers, together with certified space-bounded coefficient
routines, suffice to evaluate the cleared integer polynomial modulo every
positive modulus. Reduction preserves the specified denominator width even
when leading coefficients vanish modulo the modulus.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.IntegerBits

open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Polynomial

def context (p : List Bool) : List Bool := pairFst (pairFst p)
def selectedDegree (p : List Bool) : List Bool := pairSnd (pairFst p)
abbrev mValue (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd p) + 1

theorem context_mem_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem selectedDegree_mem_FP : selectedDegree ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (context (pairFst p)) (pairSnd p)) (BinaryNat.normalize (pairSnd (pairFst p)))

def exponentQuery (p : List Bool) : List Bool := pair (context (pairFst p)) (pairSnd p)

theorem exponentQuery_mem_FP : exponentQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP context_mem_FP
  exact mem_FP_pair hc pairSnd_mem_FP

theorem sourceQuery_mem_FP : sourceQuery ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair exponentQuery_mem_FP hm
  exact mem_FP_of_eq h (fun _ => rfl)

theorem sourceQuery_pair (p payload : List Bool) : sourceQuery (pair p payload) =
    pair (pair (context p) payload) (BinaryNatCode.encode (mValue p - 1)) := by
  simp only [sourceQuery, pairFst_pair, pairSnd_pair, TermBits.normalize_code, mValue, Nat.add_sub_cancel_right]

theorem exponentQuery_pair (p payload : List Bool) : exponentQuery (pair p payload) = pair (context p) payload := by
  simp only [exponentQuery, pairFst_pair, pairSnd_pair]

structure Family where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  terms : List Bool → ℕ
  exponent : List Bool → ℕ → ℕ → ℕ
  coefficient : List Bool → ℕ → ℤ
  numerator : List Bool → ℕ → ℤ[X]
  denominator : List Bool → ℕ → ℤ[X]
  exponent_le : ∀ c r, r < terms c → ∀ i, i < arity c → exponent c r i ≤ width c

noncomputable def Family.polynomial (F : Family) (c : List Bool) : ℤ[X] :=
  Indexed.cleared (F.arity c) (F.terms c) (F.width c) (F.coefficient c) (F.exponent c) (F.numerator c) (F.denominator c)

noncomputable def coefficientResidue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

noncomputable def Family.value (F : Family) (p : List Bool) : List Bool :=
  coefficientResidue ((F.polynomial (context p)).coeff (Nat.fromBitsLE (selectedDegree p))) (mValue p)

structure Access (F : Family) where
  arity : List Bool → List Bool
  width : List Bool → List Bool
  terms : List Bool → List Bool
  exponent : List Bool → List Bool
  coefficient : List Bool → List Bool
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  arity_eq : ∀ c, Nat.fromBitsLE (arity c) = F.arity c
  width_eq : ∀ c, Nat.fromBitsLE (width c) = F.width c
  terms_eq : ∀ c, Nat.fromBitsLE (terms c) = F.terms c
  exponent_eq : ∀ c r, r < F.terms c → ∀ i, i < F.arity c →
    Nat.fromBitsLE (exponent (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) = F.exponent c r i
  coefficient_eq : ∀ c r, r < F.terms c → ∀ m, 0 < m →
    coefficient (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((F.coefficient c r : ℤ) : ZMod m)
  numerator_eq : ∀ c i, i < F.arity c → ∀ k m, 0 < m →
    numerator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((F.numerator c i).coeff k : ℤ) : ZMod m)
  denominator_eq : ∀ c i, i < F.arity c → ∀ k m, 0 < m →
    denominator (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((F.denominator c i).coeff k : ℤ) : ZMod m)

structure Access.ControlsPolyTime {F : Family} (a : Access F) : Prop where
  arity : a.arity ∈ FP
  width : a.width ∈ FP
  terms : a.terms ∈ FP
  exponent : a.exponent ∈ FP

set_option backward.isDefEq.respectTransparency false in
theorem Access.evaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (C : SpaceFunction a.coefficient) (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) :
    SpaceFunction F.value := by
  have hA := mem_FP_comp context_mem_FP ha.arity
  have hW := mem_FP_comp context_mem_FP ha.width
  have hT := mem_FP_comp context_mem_FP ha.terms
  have hE := mem_FP_comp exponentQuery_mem_FP ha.exponent
  let E := RationalSubstitution.evaluator (C.precompose sourceQuery sourceQuery_mem_FP)
    (N.precompose sourceQuery sourceQuery_mem_FP) (D.precompose sourceQuery sourceQuery_mem_FP)
    (a.arity ∘ context) (a.width ∘ context) (a.terms ∘ context) (a.exponent ∘ exponentQuery) pairSnd selectedDegree
    hA hW hT hE pairSnd_mem_FP selectedDegree_mem_FP
    (fun p => F.exponent (context p))
    (fun p r => (F.coefficient (context p) r : ZMod (mValue p)))
    (fun p i => (F.numerator (context p) i).map (Int.castRingHom (ZMod (mValue p))))
    (fun p i => (F.denominator (context p) i).map (Int.castRingHom (ZMod (mValue p))))
    (by
      intro p r hr i hi
      simpa only [Function.comp_apply, a.terms_eq, a.arity_eq, a.width_eq] using
        F.exponent_le (context p) r (by simpa only [Function.comp_apply, a.terms_eq] using hr)
          i (by simpa only [Function.comp_apply, a.arity_eq] using hi))
    (by
      intro p r hr i hi
      simp only [Function.comp_apply, exponentQuery_pair]
      exact a.exponent_eq _ r (by simpa only [Function.comp_apply, a.terms_eq] using hr)
        i (by simpa only [Function.comp_apply, a.arity_eq] using hi))
    (by
      intro p r hr
      simp only [Function.comp_apply, sourceQuery_pair]
      exact a.coefficient_eq _ r (by simpa only [Function.comp_apply, a.terms_eq] using hr) _ (by unfold mValue; omega))
    (by
      intro p i hi k
      simp only [Function.comp_apply, sourceQuery_pair]
      simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using
        a.numerator_eq _ i (by simpa only [Function.comp_apply, a.arity_eq] using hi) k (mValue p) (by unfold mValue; omega))
    (by
      intro p i hi k
      simp only [Function.comp_apply, sourceQuery_pair]
      simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using
        a.denominator_eq _ i (by simpa only [Function.comp_apply, a.arity_eq] using hi) k (mValue p) (by unfold mValue; omega))
  refine E.congr (funext fun p => ?_)
  simp only [RationalSubstitution.value, Function.comp_apply, a.arity_eq, a.width_eq, a.terms_eq]
  have hmap := Indexed.map_cleared (Int.castRingHom (ZMod (mValue p))) (F.arity (context p)) (F.terms (context p))
    (F.width (context p)) (F.coefficient (context p)) (F.exponent (context p)) (F.numerator (context p)) (F.denominator (context p))
  simp only [Int.coe_castRingHom] at hmap
  rw [← hmap, Polynomial.coeff_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem Family.value_packet (F : Family) (q : List Bool) (m : ℕ) (hm : 0 < m) :
    F.value (pair q (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode
      ((((F.polynomial (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))) : ZMod m).val) := by
  simp only [Family.value, mValue, context, selectedDegree, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  rfl

end LeanCanny.Algebra.RationalSubstitution.IntegerBits
