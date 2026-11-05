/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSpace
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
/-! # Indexed actual center tests keep the sampler context and word fixed

Only the coefficient selectors vary in the test datum. Chronological bank
references come from the original sampler context, through its actual common
denominator and retained scalar powers.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSource
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower MvPolynomial
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficientSource.polynomial
  FormulaSignSlotRadialCenterCoefficientSource.arity FormulaSignSlotRadialCenterCoefficientSource.degree
  FormulaSignSlotRadialCenterCoefficientSource.width FormulaSignSlotRadialCenterCoefficientSource.mass

def canonical (z : List Bool) := pair (pairFst z) (pairSnd z)
theorem canonical_FP : canonical ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP
noncomputable def allowance (source : List Bool → List Bool) (c d : List Bool) :=
  FormulaSignSlotRadialBankCenterPolynomial.allowance source (pair c d)
noncomputable def numerator (B : Bank) (refs : List Bool → List Bool) (c : List Bool) (i : ℕ) :=
  IntegralMixedFramedBankTermBits.numeratorPolynomial B.parameters B.plan B.data (B.key c)
    (Nat.fromBitsLE (WordList.get (refs c) i))
noncomputable def denominator (B : Bank) (c : List Bool) := (atKey B.parameters B.plan B.data (B.key c)).common
noncomputable def polynomial (B : Bank) (source refs : List Bool → List Bool) (c d : List Bool) :
    MvPolynomial (Fin ((atKey B.parameters B.plan B.data (B.key c)).count)) ℤ :=
  CommonDenominatorSpecialization.clear (allowance source c d) (denominator B c)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source (pair c d))) => numerator B refs c i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source (pair c d)))
noncomputable def degree (B : Bank) (source : List Bool → List Bool) (c d : List Bool) :=
  FormulaSignSlotRadialCenterCoefficientSource.degree (source (pair c d)) *
    IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (B.key c)
noncomputable def coordinateMass (B : Bank) (c : List Bool) :=
  IntegralMixedFramedBankTermBits.coordinateMass B.parameters B.plan B.data B.nodes B.factor B.seed (B.key c)
noncomputable def mass (B : Bank) (source : List Bool → List Bool) (c d : List Bool) :=
  FormulaSignSlotRadialCenterCoefficientSource.mass (source (pair c d)) + coordinateMass B c * allowance source c d

theorem degree_bound (B : Bank) (source refs : List Bool → List Bool) (c d : List Bool) :
    (polynomial B source refs c d).totalDegree ≤ degree B source c d := by
  have H := CommonDenominatorSpecialization.degree_mul (allowance source c d) (denominator B c)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source (pair c d))) => numerator B refs c i.val)
    (IntegralMixedFramedBankTermBits.maxPower B.parameters B.plan B.data (B.key c))
    (fun i => IntegralMixedFramedBankTermBits.numerator_degree _ _ _ _ _)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source (pair c d)))
  exact H.trans (Nat.mul_le_mul_right _ (FormulaSignSlotRadialCenterCoefficientSource.polynomial_degree _))

theorem allowance_degree (B : Bank) (source refs : List Bool → List Bool) (c d : List Bool) :
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source (pair c d))).totalDegree ≤ allowance source c d := by
  have H := FormulaSignSlotRadialBankCenterPolynomial.degree_allowance B source refs (pair c d)
  rw [FormulaSignSlotRadialBankCenterPolynomial.family_allowance] at H
  exact H

theorem mass_bound (B : Bank) (source refs : List Bool → List Bool) (c d : List Bool) :
    MvMass.mass (polynomial B source refs c d) ≤ 2 ^ mass B source c d := by
  have HQ : (denominator B c).natAbs ≤ 2 ^ coordinateMass B c := by
    have H := IntegralMixedFramedBankTermBits.denominator_mass B.parameters B.plan B.data
      B.nodes B.factor B.seed B.bounds (B.key c) 0
    simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvMass.C, denominator, coordinateMass] using H
  have HN (i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source (pair c d)))) :
      MvMass.mass (numerator B refs c i.val) ≤ 2 ^ coordinateMass B c :=
    IntegralMixedFramedBankTermBits.numerator_mass _ _ _ _ _ _ B.bounds _ _
  have H := CommonDenominatorSpecialization.mass (allowance source c d) (denominator B c)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (source (pair c d))) => numerator B refs c i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (source (pair c d)))
    (allowance_degree B source refs c d) (2 ^ coordinateMass B c) HQ HN
  exact H.trans ((Nat.mul_le_mul_right _
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial_mass _)).trans_eq
      (by rw [← pow_mul, ← pow_add]; rfl))

theorem sign (B : Bank) (read refs : List Bool → List Bool) (c d : List Bool)
    (raw : Fin ((atKey B.parameters B.plan B.data (B.key c)).count) → ℝ) :
    SignType.sign ((polynomial B read refs c d).eval₂ (Int.castRingHom ℝ) raw) =
      SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial (read (pair c d))).eval₂
        (Int.castRingHom ℝ) (fun i => IntegralMixedFramedBankTermSign.point B.parameters B.plan B.data
          (B.key c) raw (Nat.fromBitsLE (WordList.get (refs c) i.val)))) := by
  have HQ : (denominator B c : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero _ _ _ _)
  have HP : 0 < (denominator B c : ℝ) ^ allowance read c d := by
    change 0 < (denominator B c : ℝ) ^ (FormulaSignSlotRadialCenterCoefficientSource.arity (read (pair c d)) *
      (2 * 2 ^ FormulaSignSlotRadialCenterCoefficientSource.width (read (pair c d))))
    rw [show FormulaSignSlotRadialCenterCoefficientSource.arity (read (pair c d)) *
        (2 * 2 ^ FormulaSignSlotRadialCenterCoefficientSource.width (read (pair c d))) =
      2 * (FormulaSignSlotRadialCenterCoefficientSource.arity (read (pair c d)) *
        2 ^ FormulaSignSlotRadialCenterCoefficientSource.width (read (pair c d))) by ring, pow_mul]
    exact pow_pos (sq_pos_of_ne_zero HQ) _
  have HE := CommonDenominatorSpecialization.eval (Int.castRingHom ℝ) (allowance read c d) (denominator B c)
    (fun i : Fin (FormulaSignSlotRadialCenterCoefficientSource.arity (read (pair c d))) => numerator B refs c i.val)
    (FormulaSignSlotRadialCenterCoefficientSource.polynomial (read (pair c d))) (allowance_degree B read refs c d) HQ raw
  rw [polynomial, HE, sign_mul]
  change SignType.sign ((denominator B c : ℝ) ^ allowance read c d) * _ = _
  rw [sign_pos HP, one_mul]
  apply congrArg (fun v => SignType.sign ((FormulaSignSlotRadialCenterCoefficientSource.polynomial
    (read (pair c d))).eval₂ (Int.castRingHom ℝ) v))
  funext i
  have H := IntegralMixedFramedBankTermSign.ratio B.parameters B.plan B.data (B.key c) raw
    (Nat.fromBitsLE (WordList.get (refs c) i.val))
  simpa only [IntegralMixedFramedBankTermBits.denominatorPolynomial, MvPolynomial.eval₂_C,
    numerator, denominator] using H

noncomputable def source (B : Bank) (read refs : List Bool → List Bool) :
    SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B) where
  arity c _ := (atKey B.parameters B.plan B.data (B.key c)).count
  newer _ _ := 0
  polynomial := polynomial B read refs
  degree := degree B read
  mass := mass B read
  dimension _ _ := Nat.zero_add _
  polynomial_degree := degree_bound B read refs
  polynomial_mass := mass_bound B read refs

private def queryBase (u : List Bool) := pairFst (pairFst u)
private theorem queryBase_FP : queryBase ∈ FP := by polytime [queryBase]
private noncomputable def queryBank (B : Bank) : Bank where
  parameters := B.parameters
  plan := B.plan
  data := B.data
  nodes := B.nodes
  factor := B.factor
  seed := B.seed
  bounds := B.bounds
  key u := B.key (queryBase u)
  positive u := B.positive (queryBase u)
  coordinate u := B.coordinate (queryBase u)
private noncomputable def queryBank_access (B : Bank) (h : IntegralFramedBankQuery.Access B) :
    IntegralFramedBankQuery.Access (queryBank B) where
  parameters := h.parameters
  liftedData := h.liftedData
  controls := h.controls
  bounds := h.bounds
  nodes := h.nodes
  factor := h.factor
  seed := h.seed
  key := mem_FP_comp (f := queryBase) (g := B.key) queryBase_FP h.key
  coordinate := h.coordinate.comp queryBase_FP

theorem coefficient_evaluator (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) (hs : read ∈ FP) (hr : refs ∈ FP) :
    SpaceFunction (SquareSampleCompleteSuffixPolynomialTest.coefficient (source B read refs)) := by
  let ctx := RationalSubstitution.IntegerBits.context
  let origin := fun q => canonical (ctx q)
  have HO : origin ∈ FP := mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP canonical_FP
  have HS : (read ∘ origin) ∈ FP := mem_FP_comp HO hs
  have HR : (refs ∘ queryBase) ∈ FP := mem_FP_comp queryBase_FP hr
  have E := FormulaSignSlotRadialBankCenterSpace.row_evaluator (queryBank B) (queryBank_access B h)
    (read ∘ origin) (refs ∘ queryBase) RationalSubstitution.IntegerBits.selectedDegree pairSnd
    HS HR RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  apply E.congr
  funext q
  rfl

theorem access (B : Bank) (h : IntegralFramedBankQuery.Access B)
    (read refs : List Bool → List Bool) (hs : read ∈ FP) (hr : refs ∈ FP) : (source B read refs).Access := by
  have HS : (read ∘ canonical) ∈ FP := mem_FP_comp canonical_FP hs
  have HD : BinaryFn (fun z => degree B read (pairFst z) (pairSnd z)) :=
    BinaryFn.mul (FormulaSignSlotRadialCenterCoefficientSource.degree_binary.comp HS)
      ((IntegralMixedFramedBankTermBits.maxPower_binary B.parameters h.parameters B.plan B.data).comp
        (mem_FP_comp pairFst_mem_FP h.key))
  have HG : BinaryFn (fun z => coordinateMass B (pairFst z)) :=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary B.parameters h.parameters B.plan B.data
      h.nodes h.factor h.seed).comp (mem_FP_comp pairFst_mem_FP h.key)
  have HA := FormulaSignSlotRadialCenterCoefficientSource.arity_unary.comp HS
  have HW := FormulaSignSlotRadialCenterCoefficientSource.width_unary.comp HS
  have HB : BinaryFn (fun z => allowance read (pairFst z) (pairSnd z)) :=
    (BinaryFn.ofUnary HA).mul ((BinaryFn.const 2).mul ((BinaryFn.const 2).powUnary HW))
  exact ⟨UnaryFn.const 0, HD,
    BinaryFn.add (FormulaSignSlotRadialCenterCoefficientSource.mass_binary.comp HS) (HG.mul HB),
    coefficient_evaluator B h read refs hs hr⟩

end LeanCanny.Encoding.FormulaSignSlotRadialBankCenterSource
