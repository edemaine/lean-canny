/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayFixedPaddedPolynomialValue
public import LeanCanny.Algebra.MacaulayPaddedExtraneousPolynomialSpace
public import LeanCanny.Algebra.PaddedCharacteristicQuotientSpace
public import LeanCanny.Algebra.MacaulayPolynomialDeformationBounds
/-! # Native coefficients of the actual normalized universal polynomial value

One streamed original homogeneous-system coefficient routine supplies both
full Macaulay matrices. The monic characteristic quotient is computed with
the full native dimension as ceiling. No extraneous determinant is inverted.
This lower backend charges its source routine; the original formal radial
source instantiates that routine separately.
-/
@[expose] public section
namespace LeanCanny.Algebra.MacaulayNormalizedPolynomialBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MacaulayUniversal.polynomialValue

def layout (n W : List Bool → ℕ) (d : List Bool → ℕ → ℕ) : MacaulayBits.Layout where
  arity c := n c + 1
  width := W
  degree := d

def zeroQuery (q : List Bool) : List Bool :=
  pair (pair (RationalSubstitution.IntegerBits.context q) (pairSnd q))
    (pair (RationalSubstitution.IntegerBits.selectedDegree q) [])
theorem zeroQuery_FP : zeroQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)
    (mem_FP_pair RationalSubstitution.IntegerBits.selectedDegree_mem_FP (constFn_mem_FP []))

theorem atZero_evaluator (p : List Bool → Polynomial (Polynomial ℤ))
    (E : SpaceFunction (SymbolicFixedTableEntryBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => (p c).coeff 0)) := by
  refine (E.precompose zeroQuery zeroQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, SymbolicFixedTableEntryBits.coefficient, zeroQuery, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE ([] : List Bool) = 0 from rfl]
  rfl

theorem evaluator (n W : List Bool → ℕ) (d : List Bool → ℕ → ℕ)
    (p : (c : List Bool) → Fin (n c + 1) → MvPolynomial (Fin (n c + 1)) (Polynomial ℤ))
    (hL : (layout n W d).PolyTime) (B : List Bool → ℕ) (hB : BinaryFn B)
    (hp : ∀ c i e, ((p c i).coeff e).natDegree ≤ B c)
    (hhom : ∀ c i, (p c i).IsHomogeneous (d c i.val))
    (hd : ∀ c (i : Fin (n c + 1)), 0 < d c i.val)
    (hdegree : ∀ c (i : Fin (n c + 1)), d c i.val < 2 ^ W c)
    (hW : ∀ c, Macaulay.level (fun i : Fin (n c + 1) => d c i.val) < 2 ^ W c)
    (source : List Bool → List Bool) (S : SpaceFunction source)
    (hc : ∀ z (i : Fin (n (pairFst z) + 1)) r k,
      source (pair z (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode r) (BinaryNatCode.encode k)))) =
          residueBits (((((p (pairFst z) i).coeff
            (RationalSubstitution.Indexed.exponentVector (n (pairFst z) + 1)
              (FixedWidthPolynomial.entry (W (pairFst z)) r))).coeff k) : ℤ) :
                ZMod (Nat.fromBitsLE (pairSnd z) + 1))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c =>
      MacaulayUniversal.polynomialValue (fun i : Fin (n c + 1) => d c i.val) (W c)
        (hdegree c) (hW c) (p c))) := by
  let L := layout n W d
  let N := fun c => FixedWidthPolynomial.count (n c + 1) (W c)
  let A := MacaulayIntegerPolynomialBits.matrix L p
  let E := fun c => Macaulay.extraneousPadded (p c) (MacaulayBits.Degrees L c) (W c)
  have HN : ∀ c, 0 < N c := fun c => by
    change 0 < (2 ^ W c) ^ (n c + 1)
    exact pow_pos (Nat.two_pow_pos _) _
  have HBinary : BinaryFn N :=
    BinaryFn.of_bits (mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP hL.arity hL.width)
      (fun c => FixedWidthPolynomial.countCode_code (layout n W d).arity (layout n W d).width c))
  have HEven (c : List Bool) : Even (N c) := by
    have HW : 0 < W c := by
      by_contra HN
      have H0 : W c = 0 := by omega
      have HL := Macaulay.level_pos (fun i : Fin (n c + 1) => d c i.val)
      have HW := hW c
      rw [H0, pow_zero] at HW
      omega
    have HExp : 0 < W c * (n c + 1) := Nat.mul_pos HW (Nat.succ_pos _)
    obtain ⟨k, HK⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt HExp)
    change Even ((2 ^ W c) ^ (n c + 1))
    rw [← pow_mul, HK, pow_succ]
    exact ⟨2 ^ k, by ring⟩
  have HA : ∀ c i j, (A c i j).natDegree ≤ B c := fun c =>
    Macaulay.polynomial_entry_degree_le (p c) (MacaulayBits.Degrees L c) (W c) (B c) (hp c)
  have HE : ∀ c i j, (E c i j).natDegree ≤ B c := by
    intro c i j
    simp only [E, Macaulay.extraneousPadded, PrincipalPadding.matrix]
    split_ifs
    · exact HA c i j
    · rw [Matrix.one_apply]
      split_ifs <;> simp
  let sourceA := MacaulayIntegerPolynomialBits.entry L source
  have SA := MacaulayIntegerPolynomialBits.entry_evaluator ⟨hL.arity, hL.width, BinaryFn.ofUnary hL.degree⟩ S
  have hcA := MacaulayIntegerPolynomialBits.entry_packet L p source hc
  let sourceE := MacaulayPaddedExtraneousPolynomialBits.entry L sourceA
  have SE := MacaulayPaddedExtraneousPolynomialBits.entry_evaluator L hL sourceA SA
  have hcE := MacaulayPaddedExtraneousPolynomialBits.entry_packet L p sourceA hcA
  have HQ := PaddedCharacteristicQuotientBits.evaluator N N B A E HN HEven HBinary HBinary hB
    HA HE sourceA sourceE SA SE hcA hcE
  let P := fun c => ScaledPolynomialQuotient.quotient (E c).charpoly
    ((A c).charpoly * (1 - Polynomial.X) ^ N c) (N c) (N c)
  have HZero := atZero_evaluator P HQ
  have HValue (c : List Bool) : (P c).coeff 0 =
      MacaulayUniversal.polynomialValue (fun i : Fin (n c + 1) => d c i.val) (W c)
        (hdegree c) (hW c) (p c) := by
    change (MacaulayFixedPaddedPolynomialValue.quotient (p c)
      (fun i => d c i.val) (W c)).coeff 0 = _
    exact (MacaulayFixedPaddedPolynomialValue.value_eq_coefficient_zero _ _
      (hdegree c) (hW c) _ (hhom c) (hd c)).symm
  have HFamily := funext HValue
  rw [HFamily] at HZero
  exact HZero


end LeanCanny.Algebra.MacaulayNormalizedPolynomialBits
