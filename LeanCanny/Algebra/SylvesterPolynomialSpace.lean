/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialMomentSpace
public import LeanCanny.Algebra.SylvesterSpaceAccess

/-!
# Space-certified coefficients of polynomial Sylvester entries

The scalar Sylvester accessor is reused with a context carrying the requested
coefficient degree. Its coefficient children receive the original polynomial
index and that degree. No polynomial entry or coefficient list is stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterPolynomialBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open Polynomial

structure Access where
  leftDegree : List Bool → List Bool
  rightDegree : List Bool → List Bool
  modulus : List Bool → List Bool
  degree : List Bool → List Bool
  leftCoefficient : List Bool → List Bool
  rightCoefficient : List Bool → List Bool

structure Access.ControlsPolyTime (a : Access) : Prop where
  leftDegree : a.leftDegree ∈ FP
  rightDegree : a.rightDegree ∈ FP
  modulus : a.modulus ∈ FP
  degree : a.degree ∈ FP

namespace Access

def scalarBits (a : Access) : SylvesterBits.Access where
  leftDegree := a.leftDegree
  rightDegree := a.rightDegree
  coefficientBits := fun _ => []
  leftCoefficient := a.leftCoefficient ∘ PolynomialMoment.vectorInput
  rightCoefficient := a.rightCoefficient ∘ PolynomialMoment.vectorInput

theorem scalar_controls (a : Access) (ha : a.ControlsPolyTime) : a.scalarBits.ControlsPolyTime :=
  ⟨ha.leftDegree, ha.rightDegree, constFn_mem_FP []⟩

def entry (a : Access) : List Bool → List Bool :=
  SylvesterBits.entry a.scalarBits ∘ PolynomialMoment.augmentedInput

noncomputable def entryEvaluator (a : Access) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.leftCoefficient) (R : SpaceFunction a.rightCoefficient) : SpaceFunction a.entry := by
  have EL := L.precompose PolynomialMoment.vectorInput PolynomialMoment.vectorInput_mem_FP
  have ER := R.precompose PolynomialMoment.vectorInput PolynomialMoment.vectorInput_mem_FP
  have S := SylvesterBits.entryEvaluator a.scalarBits (scalar_controls a ha) EL ER
  exact S.precompose PolynomialMoment.augmentedInput PolynomialMoment.augmentedInput_mem_FP

theorem entry_correct {R : Type*} [Semiring R] (a : Access) (c : List Bool)
    (f g : Polynomial (Polynomial R)) (m n D : ℕ) (enc : R → List Bool)
    (hm : a.leftDegree c = BinaryNatCode.encode m) (hn : a.rightDegree c = BinaryNatCode.encode n)
    (hf : ∀ k, a.leftCoefficient (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode D))) =
      enc ((f.coeff k).coeff D))
    (hg : ∀ k, a.rightCoefficient (pair c (pair (BinaryNatCode.encode k) (BinaryNatCode.encode D))) =
      enc ((g.coeff k).coeff D))
    (hz : enc 0 = []) (i j : Fin (m + n)) :
    a.entry (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode D)))) =
      enc ((Polynomial.sylvester f g m n i j).coeff D) := by
  simp only [entry, PolynomialMoment.augmentedInput, Function.comp_apply, pairFst_pair, pairSnd_pair]
  apply SylvesterBits.entry_correct a.scalarBits (pair c (BinaryNatCode.encode D)) f g m n
    (fun p => enc (p.coeff D))
  constructor
  · simpa only [scalarBits, pairFst_pair] using hm
  · simpa only [scalarBits, pairFst_pair] using hn
  · intro k
    simpa only [scalarBits, Function.comp_apply, PolynomialMoment.vectorInput, pairFst_pair, pairSnd_pair] using hf k
  · intro k
    simpa only [scalarBits, Function.comp_apply, PolynomialMoment.vectorInput, pairFst_pair, pairSnd_pair] using hg k
  · simpa only [Polynomial.coeff_zero] using hz

def dimension (a : Access) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.leftDegree c) (a.rightDegree c))

theorem dimension_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.dimension ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.leftDegree ha.rightDegree) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.dimension) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem dimension_code (a : Access) (c : List Bool) (m n : ℕ)
    (hm : a.leftDegree c = BinaryNatCode.encode m) (hn : a.rightDegree c = BinaryNatCode.encode n) :
    a.dimension c = BinaryNatCode.encode (m + n) := by
  simp only [dimension, hm, hn, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end Access
end LeanCanny.Algebra.SylvesterPolynomialBits
