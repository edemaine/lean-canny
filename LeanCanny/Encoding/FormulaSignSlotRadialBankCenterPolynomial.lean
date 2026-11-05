/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientSource
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
public import LeanCanny.Algebra.FixedWidthCommonDenominatorSpace
public import LeanCanny.Algebra.CommonDenominatorMass
/-! # Actual center coefficients pulled back through chronological bank fields

The local reference table chooses chronological producers in one unchanged
bank. Invalid references have the actual zero extension. Even common clearing
preserves signs, including negative nonunit stored denominators.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBankCenterPolynomial
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask MvPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficientSource.polynomial

def key (B : Bank) (z : List Bool) := B.key (pairFst z)
def reference (refs : List Bool → List Bool) (z : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (refs (pairFst z)) i)
noncomputable def numerator (B : Bank) (refs : List Bool → List Bool) (z : List Bool) (i : ℕ) :=
  IntegralMixedFramedBankTermBits.numeratorPolynomial B.parameters B.plan B.data (key B z) (reference refs z i)
noncomputable def denominator (B : Bank) (z : List Bool) := (atKey B.parameters B.plan B.data (key B z)).common

noncomputable def degree (B : Bank) (source : List Bool → List Bool) (z : List Bool) :=
  FormulaSignSlotRadialCenterCoefficientSource.degree (source z) *
    IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (key B z)
noncomputable def width (B : Bank) (source : List Bool → List Bool) (z : List Bool) := (degree B source z).size

noncomputable def family (B : Bank) (source refs : List Bool → List Bool) : FixedWidthCommonDenominatorBits.Family where
  sourceArity z := FormulaSignSlotRadialCenterCoefficientSource.arity (source z)
  sourceWidth z := FormulaSignSlotRadialCenterCoefficientSource.width (source z)
  targetArity z := (atKey B.parameters B.plan B.data (key B z)).count
  targetWidth := width B source
  source z := FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z)
  denominator := denominator B
  numerator := numerator B refs
  source_fit z i := (degreeOf_le_totalDegree _ i).trans_lt
    ((FormulaSignSlotRadialCenterCoefficientSource.polynomial_degree (source z)).trans_lt (Nat.lt_size_self _))

attribute [local irreducible] FormulaSignSlotRadialCenterCoefficientSource.arity
  FormulaSignSlotRadialCenterCoefficientSource.width FormulaSignSlotRadialCenterCoefficientSource.degree
  FormulaSignSlotRadialCenterCoefficientSource.mass

noncomputable def polynomial (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    MvPolynomial (Fin ((atKey B.parameters B.plan B.data (key B z)).count)) ℤ :=
  CommonDenominatorSpecialization.clear ((family B source refs).allowance z) (denominator B z)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source z)) => numerator B refs z i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z))

theorem family_polynomial (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    (family B source refs).polynomial z = polynomial B source refs z := rfl

theorem key_FP (B : Bank) (h : IntegralFramedBankQuery.Access B) : key B ∈ FP := mem_FP_comp pairFst_mem_FP h.key
theorem targetArity_unary (B : Bank) (h : IntegralFramedBankQuery.Access B) :
    UnaryFn (family B (fun _ => []) (fun _ => [])).targetArity :=
  (IntegralMixedFramedBankSnapshotBits.count_unary B.parameters h.parameters B.plan B.data).comp (key_FP B h)
theorem degree_binary (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source : List Bool → List Bool) (hs : source ∈ FP) : BinaryFn (degree B source) :=
  BinaryFn.mul (FormulaSignSlotRadialCenterCoefficientSource.degree_binary.comp hs)
    ((IntegralMixedFramedBankTermBits.maxPower_binary B.parameters h.parameters B.plan B.data).comp (key_FP B h))
theorem width_unary (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source : List Bool → List Bool) (hs : source ∈ FP) : UnaryFn (width B source) :=
  (UnaryFn.length (degree_binary B h source hs).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

theorem numerator_degree (B : Bank) (refs : List Bool → List Bool) (z : List Bool) (i : ℕ) :
    (numerator B refs z i).totalDegree ≤ IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (key B z) :=
  IntegralMixedFramedBankTermBits.numerator_degree _ _ _ _ _

theorem polynomial_degree (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    (polynomial B source refs z).totalDegree ≤ degree B source z := by
  have H := CommonDenominatorSpecialization.degree_mul ((family B source refs).allowance z)
    (denominator B z)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source z)) => numerator B refs z i.val)
    (IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (key B z))
    (fun i => numerator_degree B refs z i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z))
  exact H.trans (Nat.mul_le_mul_right _
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial_degree (source z)))

theorem support_fit (B : Bank) (source refs : List Bool → List Bool) (z : List Bool)
    (e : Fin ((atKey B.parameters B.plan B.data (key B z)).count) →₀ ℕ)
    (he : e ∈ (polynomial B source refs z).support) (i) : e i < 2 ^ width B source z :=
  ((monomial_le_degreeOf i he).trans ((degreeOf_le_totalDegree _ i).trans
    (polynomial_degree B source refs z))).trans_lt (Nat.lt_size_self _)

private theorem box_degree (a w : ℕ) (p : MvPolynomial (Fin a) ℤ)
    (hp : ∀ i, p.degreeOf i < 2 ^ w) : p.totalDegree ≤ a * (2 * 2 ^ w) := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ _ : Fin a, 2 * 2 ^ w := Finset.sum_le_sum (fun i _ =>
      (monomial_le_degreeOf i he).trans ((hp i).le.trans (by omega)))
    _ = _ := by simp

theorem degree_allowance (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    ((family B source refs).source z).totalDegree ≤ (family B source refs).allowance z :=
  box_degree _ _ _ ((family B source refs).source_fit z)

noncomputable def coordinateMass (B : Bank) (z : List Bool) :=
  IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (key B z)
noncomputable def allowance (source : List Bool → List Bool) (z : List Bool) :=
  FormulaSignSlotRadialCenterCoefficientSource.arity (source z) *
    (2 * 2 ^ FormulaSignSlotRadialCenterCoefficientSource.width (source z))
theorem family_allowance (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    (family B source refs).allowance z = allowance source z := by
  simp only [FixedWidthCommonDenominatorBits.Family.allowance, family, allowance]
noncomputable def mass (B : Bank) (source _refs : List Bool → List Bool) (z : List Bool) :=
  FormulaSignSlotRadialCenterCoefficientSource.mass (source z) +
    coordinateMass B z * allowance source z

theorem mass_binary (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (source refs : List Bool → List Bool) (hs : source ∈ FP) : BinaryFn (mass B source refs) := by
  have HG : BinaryFn (coordinateMass B) :=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary B.parameters h.parameters B.plan B.data
      h.nodes h.factor h.seed).comp (key_FP B h)
  have HA : UnaryFn (fun z => FormulaSignSlotRadialCenterCoefficientSource.arity (source z)) :=
    FormulaSignSlotRadialCenterCoefficientSource.arity_unary.comp hs
  have HW : UnaryFn (fun z => FormulaSignSlotRadialCenterCoefficientSource.width (source z)) :=
    FormulaSignSlotRadialCenterCoefficientSource.width_unary.comp hs
  have HB : BinaryFn (allowance source) :=
    (BinaryFn.ofUnary HA).mul ((BinaryFn.const 2).mul ((BinaryFn.const 2).powUnary HW))
  exact BinaryFn.add (FormulaSignSlotRadialCenterCoefficientSource.mass_binary.comp hs) (HG.mul HB)

theorem polynomial_mass (B : Bank) (source refs : List Bool → List Bool) (z : List Bool) :
    MvMass.mass (polynomial B source refs z) ≤ 2 ^ mass B source refs z := by
  have HQ : (denominator B z).natAbs ≤ 2 ^ coordinateMass B z := by
    have H := IntegralMixedFramedBankTermBits.denominator_mass B.parameters B.plan B.data
      B.nodes B.factor B.seed B.bounds (key B z) 0
    simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvMass.C, denominator, coordinateMass] using H
  have HN (i : Fin ((family B source refs).sourceArity z)) :
      MvMass.mass (numerator B refs z i.val) ≤ 2 ^ coordinateMass B z :=
    IntegralMixedFramedBankTermBits.numerator_mass _ _ _ _ _ _ B.bounds _ _
  have H := CommonDenominatorSpecialization.mass ((family B source refs).allowance z) (denominator B z)
    (fun i : Fin ((family B source refs).sourceArity z) => numerator B refs z i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z))
    (degree_allowance B source refs z) (2 ^ coordinateMass B z) HQ HN
  exact H.trans ((Nat.mul_le_mul_right _
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial_mass (source z))).trans_eq
      (by rw [← pow_mul, ← pow_add, family_allowance]; rfl))

theorem sign (B : Bank) (source refs : List Bool → List Bool) (z : List Bool)
    (raw : Fin ((atKey B.parameters B.plan B.data (key B z)).count) → ℝ) :
    SignType.sign ((polynomial B source refs z).eval₂ (Int.castRingHom ℝ) raw) =
      SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z)).eval₂ (Int.castRingHom ℝ)
        (fun i => IntegralMixedFramedBankTermSign.point B.parameters B.plan B.data (key B z) raw (reference refs z i.val))) := by
  have HQ : (denominator B z : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero _ _ _ _)
  have HP : 0 < (denominator B z : ℝ) ^ (family B source refs).allowance z := by
    change 0 < (denominator B z : ℝ) ^ ((family B source refs).sourceArity z * (2 * 2 ^ (family B source refs).sourceWidth z))
    rw [show (family B source refs).sourceArity z * (2 * 2 ^ (family B source refs).sourceWidth z) =
      2 * ((family B source refs).sourceArity z * 2 ^ (family B source refs).sourceWidth z) by ring, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero HQ) _
  have HD : (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z)).totalDegree ≤
      (family B source refs).allowance z := degree_allowance B source refs z
  have HE := CommonDenominatorSpecialization.eval (Int.castRingHom ℝ) ((family B source refs).allowance z)
    (denominator B z)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source z)) => numerator B refs z i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z)) HD HQ raw
  rw [polynomial, HE, sign_mul]
  change SignType.sign ((denominator B z : ℝ) ^ (family B source refs).allowance z) * _ = _
  rw [sign_pos HP, one_mul]
  apply congrArg (fun v => SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial (source z)).eval₂ (Int.castRingHom ℝ) v))
  funext i
  have H := IntegralMixedFramedBankTermSign.ratio B.parameters B.plan B.data (key B z) raw (reference refs z i.val)
  simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvPolynomial.eval₂_C,
    numerator, denominator] using H

end LeanCanny.Encoding.FormulaSignSlotRadialBankCenterPolynomial
