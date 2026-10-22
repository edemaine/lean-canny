/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveNativeOriginalResidue
public import LeanCanny.ETR.CoercivePreparationControls
public import LeanCanny.Algebra.DyadicPolynomialSpace
public import LeanCanny.Algebra.FiniteSourceDegreePreparation
public import LeanCanny.Algebra.SquarefreeGCDSpace
public import LeanCanny.Algebra.BalancedCanonicalDegrees
public import LeanCanny.Algebra.SymbolicScaledQuotientSpace
public import LeanCanny.Algebra.PaddedAnnihilatorPreparation

/-! # Native integer reference leaves for the actual coercive source -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveIntegerPreparation
open Polynomial LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling
open SymbolicScaledQuotientBits (original modulus alpha target original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det
  CoerciveNativeAnnihilators.original CoerciveNativeAnnihilators.degreeBound
  CoerciveNativeAnnihilators.massExponent CoerciveSourceSampling.dimension
  ArithmeticBits.one BinaryNat.succ BinaryNat.normalize
  CoercivePreparationControls.referenceCode CoercivePreparationControls.referenceExponent
set_option backward.isDefEq.respectTransparency false

noncomputable def raw (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (CoercivePreparationControls.family (pairFst c)).padded (Nat.fromBitsLE (pairSnd c))

noncomputable def dyadicFamily : DyadicPolynomialBits.Family where
  polynomial := raw
  degree c := BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c)+1)
  parameterDegree c := BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c))
  exponent c := CoercivePreparationControls.referenceCode (pairFst c)
  mass c := BinaryNatCode.encode (CoerciveNativeAnnihilators.massExponent (pairFst c))
  polynomial_degree c := by
    simpa only [raw, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      SymbolicFixedTableFinite.Family.paddedBudget, CoercivePreparationControls.family, CoercivePreparationControls.budget] using
      ((CoercivePreparationControls.family (pairFst c)).padded_controls (Nat.fromBitsLE (pairSnd c))).1
  coefficient_degree c i := by
    simpa only [raw, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      SymbolicFixedTableFinite.Family.paddedBudget, CoercivePreparationControls.family, CoercivePreparationControls.budget] using
      ((CoercivePreparationControls.family (pairFst c)).padded_controls (Nat.fromBitsLE (pairSnd c))).2.1 i
  coefficient_mass c i := by
    simpa only [raw, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      SymbolicFixedTableFinite.Family.paddedBudget, CoercivePreparationControls.family, CoercivePreparationControls.budget] using
      ((CoercivePreparationControls.family (pairFst c)).padded_controls (Nat.fromBitsLE (pairSnd c))).2.2 i

theorem dyadic_controls : DyadicPolynomialBits.ControlsPolyTime dyadicFamily := by
  constructor
  · change (fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c)+1)) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound c+1))
      pairFst_mem_FP (CoerciveNativeAnnihilators.degreeBound_binary.add (BinaryFn.const 1)).bits_mem_FP
  · change (fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c))) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound c))
      pairFst_mem_FP CoerciveNativeAnnihilators.degreeBound_binary.bits_mem_FP
  · change (CoercivePreparationControls.referenceCode ∘ pairFst) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := CoercivePreparationControls.referenceCode) pairFst_mem_FP CoercivePreparationControls.referenceCode_mem_FP
  · change (fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.massExponent (pairFst c))) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (CoerciveNativeAnnihilators.massExponent c))
      pairFst_mem_FP CoerciveNativeAnnihilators.massExponent_binary.bits_mem_FP

theorem dyadic_polynomial (c : List Bool) : dyadicFamily.polynomial c = raw c := rfl
theorem dyadic_degree (c : List Bool) : dyadicFamily.degree c = BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c)+1) := rfl
theorem dyadic_parameterDegree (c : List Bool) : dyadicFamily.parameterDegree c = BinaryNatCode.encode (CoerciveNativeAnnihilators.degreeBound (pairFst c)) := rfl
theorem dyadic_exponent (c : List Bool) : dyadicFamily.exponent c = CoercivePreparationControls.referenceCode (pairFst c) := rfl
theorem dyadic_mass (c : List Bool) : dyadicFamily.mass c = BinaryNatCode.encode (CoerciveNativeAnnihilators.massExponent (pairFst c)) := rfl
attribute [local irreducible] dyadicFamily DyadicPolynomialBits.Family.specialized

noncomputable def rawCoefficient : List Bool → List Bool := SymbolicFixedTableEntryBits.coefficient raw

theorem rawEvaluator : SpaceFunction rawCoefficient := by
  let input := pairFst ∘ original
  let index := pairSnd ∘ original
  have hi : input ∈ FP := mem_FP_comp original_FP pairFst_mem_FP
  have hj : index ∈ FP := mem_FP_comp original_FP pairSnd_mem_FP
  have E := CoerciveNativeOriginalResidue.evaluator hi hj target_FP alpha_FP modulus_FP
  have hone := mem_FP_comp (mem_FP_comp (f := modulus) (g := BinaryNat.succ) modulus_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  have hpad := ((BinaryNat.eq_const_fppred target_FP 1).and (BinaryNat.eq_const_fppred alpha_FP 0)).ite_mem_FP hone (constFn_mem_FP [])
  have hcount := bits_mem_FP (((dimension_unary.comp hi).add (UnaryFn.const 1)))
  have hvalid := BinaryNat.lt_fppred hj hcount
  have R := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (index q)<dimension (input q)+1))
    (hvalid.of_iff (fun q => by simp only [Nat.fromBitsLE_bits])).flag_mem_FP E (SpaceFunction.ofFP _ hpad)
  refine R.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq]
  by_cases hv : Nat.fromBitsLE (index q)<dimension (input q)+1
  · simp only [hv, ite_true, rawCoefficient, SymbolicFixedTableEntryBits.coefficient, raw,
      SymbolicFixedTableFinite.Family.padded, CoercivePreparationControls.family]
    change _ = SymbolicFixedTableEntryBits.integerResidue ((((if Nat.fromBitsLE (index q)<dimension (input q)+1 then
      CoerciveNativeAnnihilators.original (input q) (Nat.fromBitsLE (index q)) else X).coeff
        (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q)))) (Nat.fromBitsLE (modulus q)+1)
    rw [ite_eq_left hv]
    rfl
  · simp only [hv, ite_false, rawCoefficient, SymbolicFixedTableEntryBits.coefficient, raw,
      SymbolicFixedTableFinite.Family.padded, CoercivePreparationControls.family]
    change _ = SymbolicFixedTableEntryBits.integerResidue ((((if Nat.fromBitsLE (index q)<dimension (input q)+1 then
      CoerciveNativeAnnihilators.original (input q) (Nat.fromBitsLE (index q)) else X).coeff
        (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q)))) (Nat.fromBitsLE (modulus q)+1)
    rw [ite_eq_right hv]
    let m := Nat.fromBitsLE (modulus q)+1
    let : NeZero m := ⟨by dsimp [m]; omega⟩
    have hw : BinaryNat.succ (modulus q)=BinaryNatCode.encode m := by rw [BinaryNat.succ_eq_bits]; rfl
    have hx (k l : ℕ) : (((X : Polynomial (Polynomial ℤ)).coeff k).coeff l) =
        (if k=1 ∧ l=0 then (1 : ℤ) else 0) := by
      by_cases hk : k=1
      · subst k
        simp only [coeff_X, ite_true, true_and, coeff_one, eq_self]
      · simp only [coeff_X, Ne.symm hk, hk, ite_false, false_and, coeff_zero]
    rw [hx]
    simp only [Function.comp_apply]
    by_cases h : Nat.fromBitsLE (target q)=1 ∧ Nat.fromBitsLE (alpha q)=0
    · simp only [h, SymbolicFixedTableEntryBits.integerResidue, hw]
      exact ArithmeticBits.one_residueBits m
    · simp only [h, ite_false, SymbolicFixedTableEntryBits.integerResidue, Int.cast_zero,
        residueBits, BinaryNatCode.encode, ZMod.val_zero]
      rfl

def dyadicQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q))
    (pair (pairSnd (pairSnd (pairFst q))) (pairFst (pairSnd (pairFst q))))
theorem dyadicQuery_FP : dyadicQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP))

attribute [local irreducible] rawCoefficient dyadicQuery

noncomputable def dyadicAccess : DyadicPolynomialBits.Access dyadicFamily where
  coefficient := rawCoefficient ∘ dyadicQuery
  coefficient_eq c i j m hm := by
    simp only [Function.comp_apply, rawCoefficient, SymbolicFixedTableEntryBits.coefficient,
      dyadicQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, dyadic_polynomial,
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
    rfl

theorem dyadic_coefficient : @DyadicPolynomialBits.Access.coefficient dyadicFamily dyadicAccess = rawCoefficient ∘ dyadicQuery := by
  unfold dyadicAccess
  rfl
attribute [local irreducible] dyadicAccess

theorem clearEvaluator : SpaceFunction (PrimitivePairBits.coefficient dyadicFamily.specialized) := by
  have ER : SpaceFunction (@DyadicPolynomialBits.Access.coefficient dyadicFamily dyadicAccess) := by
    rw [dyadic_coefficient]
    exact rawEvaluator.precompose dyadicQuery dyadicQuery_FP
  have E : SpaceFunction dyadicFamily.residue :=
    DyadicPolynomialBits.residueEvaluator (F := dyadicFamily) dyadicAccess dyadic_controls ER
  exact E.congr (funext fun q => by
    simp only [DyadicPolynomialBits.Family.residue, PrimitivePairBits.coefficient,
      DyadicBits.mValue, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue]
    rfl)

theorem clear_eq (c : List Bool) : dyadicFamily.specialized c =
    SymbolicFixedTable.clear (raw c) (CoerciveNativeAnnihilators.degreeBound (pairFst c))
      (CoercivePreparationControls.referenceExponent (pairFst c)) := by
  ext k
  simp only [DyadicPolynomialBits.Family.specialized, DyadicPolynomial.coeff_specialize,
    dyadic_polynomial, dyadic_parameterDegree, dyadic_exponent, BinaryNatCode.encode,
    CoercivePreparationControls.referenceCode, Nat.fromBitsLE_bits, SymbolicFixedTable.clear_coeff]

theorem raw_nonzero (c : List Bool) : raw c ≠ 0 :=
  (CoercivePreparationControls.family (pairFst c)).padded_nonzero (Nat.fromBitsLE (pairSnd c))

theorem raw_controls (c : List Bool) :
    (CoercivePreparationControls.family (pairFst c)).paddedBudget.Controls (raw c) := by
  unfold raw
  exact (CoercivePreparationControls.family (pairFst c)).padded_controls _

theorem padded_inner (c : List Bool) :
    (CoercivePreparationControls.family (pairFst c)).paddedBudget.innerDegree =
      CoerciveNativeAnnihilators.degreeBound (pairFst c) := rfl

theorem leaf_sufficient (c : List Bool) :
    (CoercivePreparationControls.family (pairFst c)).paddedBudget.testExponent ≤
      CoercivePreparationControls.referenceExponent (pairFst c) :=
  (show (CoercivePreparationControls.family (pairFst c)).paddedBudget.testExponent ≤
      SymbolicFixedTable.preparationExponent (CoercivePreparationControls.family (pairFst c)).paddedBudget
        (dimension (pairFst c)+1).size from Nat.le_add_right _ _).trans
    (CoercivePreparationControls.preparation_le_reference (pairFst c))

theorem clear_nonzero (c : List Bool) : dyadicFamily.specialized c ≠ 0 := by
  rw [clear_eq]
  have H := (CoercivePreparationControls.family (pairFst c)).paddedBudget.clear_ne_zero
    (raw c) (raw_controls c) (raw_nonzero c) (CoercivePreparationControls.referenceExponent (pairFst c)) (leaf_sufficient c)
  simpa only [padded_inner] using H

theorem clear_degree (c : List Bool) : (dyadicFamily.specialized c).natDegree=(raw c).natDegree := by
  rw [clear_eq]
  have H := (CoercivePreparationControls.family (pairFst c)).paddedBudget.cleared_degree
    (raw c) (raw_controls c) (CoercivePreparationControls.referenceExponent (pairFst c)) (leaf_sufficient c)
  simpa only [padded_inner] using H

theorem clear_gcd_degree (c : List Bool) : ScaledSquarefree.degree (dyadicFamily.specialized c)=
    SymbolicScaledSquarefree.degree (raw c) := by
  rw [clear_eq]
  have H := (CoercivePreparationControls.family (pairFst c)).paddedBudget.cleared_gcd_degree
    (raw c) (raw_controls c) (raw_nonzero c) (CoercivePreparationControls.referenceExponent (pairFst c)) (leaf_sufficient c)
  simpa only [padded_inner] using H

noncomputable def sourceMass (bits : List Bool) : ℕ :=
  Nat.fromBitsLE (DyadicPolynomialBits.massCode dyadicFamily (pair bits []))

theorem sourceMass_binary : BinaryFn sourceMass := BinaryFn.fromBits
  (mem_FP_comp (f := fun bits => pair bits []) (g := DyadicPolynomialBits.massCode dyadicFamily)
    (mem_FP_pair id_mem_FP (constFn_mem_FP [])) (DyadicPolynomialBits.massCode_mem_FP dyadicFamily dyadic_controls))

theorem massCode_value (c : List Bool) : Nat.fromBitsLE (DyadicPolynomialBits.massCode dyadicFamily c)=sourceMass (pairFst c) := by
  rw [sourceMass, DyadicPolynomialBits.massCode_value, DyadicPolynomialBits.massCode_value]
  simp only [dyadic_degree, dyadic_parameterDegree, dyadic_exponent, dyadic_mass, pairFst_pair]

noncomputable def sourceFamily : SeparableBits.Family where
  polynomial := dyadicFamily.specialized
  height c := sourceMass (pairFst c)
  coefficient_bound c k := (coeff_natAbs_le_coefficientMass _ k).trans
    ((DyadicPolynomialBits.specialized_mass dyadicFamily c).trans_eq (congrArg (2^·) (massCode_value c)))

noncomputable def count (bits : List Bool) : ℕ := 2*(dimension bits+2)
theorem count_unary : UnaryFn count := (UnaryFn.const 2).mul (dimension_unary.add (UnaryFn.const 2))
noncomputable def degreeBound (bits : List Bool) : ℕ := CoerciveNativeAnnihilators.degreeBound bits+1
theorem degreeBound_binary : BinaryFn degreeBound := CoerciveNativeAnnihilators.degreeBound_binary.add (BinaryFn.const 1)

theorem source_degree (c : List Bool) (i : ℕ) (_hi : i<count c) :
    (sourceFamily.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ degreeBound c := by
  change (dyadicFamily.specialized (pair c (BinaryNatCode.encode i))).natDegree ≤ CoerciveNativeAnnihilators.degreeBound c+1
  simpa only [dyadic_degree, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
    DyadicPolynomialBits.specialized_degree dyadicFamily (pair c (BinaryNatCode.encode i))

theorem source_mass (c : List Bool) (i : ℕ) (_hi : i<count c) :
    coefficientMass (sourceFamily.polynomial (pair c (BinaryNatCode.encode i))) ≤ 2^sourceMass c := by
  change coefficientMass (dyadicFamily.specialized (pair c (BinaryNatCode.encode i))) ≤ 2^sourceMass c
  simpa only [massCode_value, pairFst_pair] using DyadicPolynomialBits.specialized_mass dyadicFamily (pair c (BinaryNatCode.encode i))

noncomputable def degreePrepare : List Bool → List Bool :=
  FiniteSourceDegreePreparation.prepare sourceFamily count degreeBound

theorem degreePrepareEvaluator : SpaceFunction degreePrepare :=
  FiniteSourceDegreePreparation.prepareEvaluator sourceFamily count degreeBound sourceMass
    source_degree source_mass count_unary degreeBound_binary sourceMass_binary clearEvaluator

noncomputable def checkedFamily : SeparableBits.Family :=
  FiniteSourceDegreePreparation.family sourceFamily count degreeBound sourceMass source_mass

noncomputable def checkedReaders : SeparableBits.Readers checkedFamily :=
  FiniteSourceDegreePreparation.readers sourceFamily count degreeBound sourceMass source_degree source_mass
    count_unary degreeBound_binary sourceMass_binary clearEvaluator

theorem checked_degree (c : List Bool) (i : ℕ) :
    (checkedFamily.polynomial (pair c (BinaryNatCode.encode i))).natDegree <
      2^FiniteSourceDegreePreparation.width degreeBound (pairFst c) :=
  FiniteSourceDegreePreparation.family_degree sourceFamily count degreeBound sourceMass source_mass c i

theorem prepared_polynomial (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    checkedFamily.polynomial (pair (degreePrepare bits) (BinaryNatCode.encode i)) =
      dyadicFamily.specialized (pair bits (BinaryNatCode.encode i)) :=
  FiniteSourceDegreePreparation.prepared_polynomial sourceFamily count degreeBound sourceMass
    source_degree source_mass bits i hi

noncomputable def gcdCode (p : List Bool) : List Bool :=
  BinaryNatCode.encode (ScaledSquarefree.degree (checkedFamily.polynomial p))

theorem gcdCodeEvaluator : SpaceFunction gcdCode :=
  (SeparableBits.gcdDegreeEvaluator checkedFamily checkedReaders).congr (funext fun p => by
    simp only [gcdCode, ScaledSquarefree.degree, PolynomialGCDBits.degree, SquarefreePart.common, derivative_map])

noncomputable def gcdPrepare (c : List Bool) : List Bool := pair c
  (FixedWidthNatVector.encode (count (pairFst c)) (FiniteSourceDegreePreparation.width degreeBound (pairFst c))
    (fun i => ScaledSquarefree.degree (checkedFamily.polynomial (pair c (BinaryNatCode.encode i)))))

theorem gcdPrepareEvaluator : SpaceFunction gcdPrepare := by
  have E := FixedWidthNatVector.encodeEvaluator (count ∘ pairFst)
    (FiniteSourceDegreePreparation.width degreeBound ∘ pairFst)
    (fun c i => ScaledSquarefree.degree (checkedFamily.polynomial (pair c (BinaryNatCode.encode i))))
    (count_unary.comp pairFst_mem_FP) ((FiniteSourceDegreePreparation.width_unary degreeBound_binary).comp pairFst_mem_FP)
    gcdCode gcdCodeEvaluator (fun _ _ => rfl)
  exact E.withInput

noncomputable def prepare : List Bool → List Bool := gcdPrepare ∘ degreePrepare

theorem prepareEvaluator : SpaceFunction prepare := degreePrepareEvaluator.chain gcdPrepareEvaluator

@[simp] theorem prepare_source (bits : List Bool) : pairFst (pairFst (prepare bits))=bits := by
  simp only [prepare, Function.comp_apply, gcdPrepare, pairFst_pair, degreePrepare,
    FiniteSourceDegreePreparation.prepare_source]

theorem checked_nonzero (p : List Bool) : checkedFamily.polynomial p ≠ 0 :=
  FiniteSourceDegreePreparation.family_nonzero sourceFamily count degreeBound sourceMass source_mass
    (fun c i _ => clear_nonzero (pair c (BinaryNatCode.encode i))) p

private theorem gcd_le (p : Polynomial ℤ) : ScaledSquarefree.degree p ≤ p.natDegree :=
  (SeparableBits.derivative_gcd_degree_le p).trans (Nat.min_le_left _ _)

noncomputable def gcdRead (q : List Bool) : List Bool :=
  FixedWidthQuery.read (fun c => count (pairFst (pairFst c)))
    (fun c => FiniteSourceDegreePreparation.width degreeBound (pairFst (pairFst c))) pairSnd q

theorem gcdRead_FP : gcdRead ∈ FP := FixedWidthQuery.read_mem_FP
  ((count_unary.comp pairFst_mem_FP).comp pairFst_mem_FP)
  (((FiniteSourceDegreePreparation.width_unary degreeBound_binary).comp pairFst_mem_FP).comp pairFst_mem_FP)
  pairSnd_mem_FP

theorem gcdRead_prepare (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    gcdRead (pair (prepare bits) (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (SymbolicScaledSquarefree.degree (raw (pair bits (BinaryNatCode.encode i)))) := by
  have hfit := (gcd_le (checkedFamily.polynomial (pair (degreePrepare bits) (BinaryNatCode.encode i)))).trans_lt
    (checked_degree (degreePrepare bits) i)
  simp only [degreePrepare, FiniteSourceDegreePreparation.prepare_source] at hfit
  rw [gcdRead, FixedWidthQuery.read_packet]
  simp only [prepare_source, hi, FixedWidthQuery.entry, ite_true]
  simp only [FixedWidthQuery.coordinate, prepare_source]
  change BinaryNatCode.encode (Nat.fromBitsLE ((pairSnd (prepare bits)).drop
    (i*FiniteSourceDegreePreparation.width degreeBound bits) |>.take
      (FiniteSourceDegreePreparation.width degreeBound bits))) = _
  simp only [prepare, Function.comp_apply, gcdPrepare, pairSnd_pair,
    degreePrepare, FiniteSourceDegreePreparation.prepare_source]
  rw [FixedWidthNatVector.decode_block _ _ _ i hi hfit]
  rw [← degreePrepare, prepared_polynomial bits i hi, clear_gcd_degree]

def retainedInput (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairSnd p)
theorem retainedInput_FP : retainedInput ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def retainedFamily : SeparableBits.Family := checkedFamily.reindex retainedInput
noncomputable def retainedReaders : SeparableBits.Readers retainedFamily := checkedReaders.reindex retainedInput retainedInput_FP
noncomputable def retainedCount (c : List Bool) : ℕ := count (pairFst (pairFst c))
noncomputable def retainedDegree (c : List Bool) : ℕ := FiniteSourceDegreePreparation.degreeBudget degreeBound (pairFst (pairFst c))
noncomputable def retainedMass (c : List Bool) : ℕ := sourceMass (pairFst (pairFst c))

theorem retainedCount_unary : UnaryFn retainedCount := (count_unary.comp pairFst_mem_FP).comp pairFst_mem_FP
theorem retainedDegree_binary : BinaryFn retainedDegree :=
  ((FiniteSourceDegreePreparation.degreeBudget_binary degreeBound_binary).comp pairFst_mem_FP).comp pairFst_mem_FP
theorem retainedMass_binary : BinaryFn retainedMass := (sourceMass_binary.comp pairFst_mem_FP).comp pairFst_mem_FP

theorem retained_nonzero (c : List Bool) (i : ℕ) (_hi : i<retainedCount c) :
    retainedFamily.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0 := by
  change checkedFamily.polynomial (retainedInput (pair c (BinaryNatCode.encode i))) ≠ 0
  exact checked_nonzero _

theorem retained_degree (c : List Bool) (i : ℕ) (_hi : i<retainedCount c) :
    (retainedFamily.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ retainedDegree c := by
  change (checkedFamily.polynomial (retainedInput (pair c (BinaryNatCode.encode i)))).natDegree ≤ _
  simp only [retainedInput, pairFst_pair, pairSnd_pair]
  exact (checked_degree (pairFst c) i).le

theorem retained_height (c : List Bool) (i : ℕ) (_hi : i<retainedCount c) :
    retainedFamily.height (pair c (BinaryNatCode.encode i)) ≤ retainedMass c := by
  change (FiniteSourceDegreePreparation.family sourceFamily count degreeBound sourceMass source_mass).height
    (retainedInput (pair c (BinaryNatCode.encode i))) ≤ _
  rw [FiniteSourceDegreePreparation.family_height]
  simp only [retainedInput, pairFst_pair]
  exact le_rfl

noncomputable def integerTable : List Bool → List Bool :=
  PaddedAnnihilatorPreparation.prepare retainedFamily retainedCount retainedDegree retainedMass

theorem integerTableEvaluator : SpaceFunction integerTable :=
  PaddedAnnihilatorPreparation.prepareEvaluator retainedFamily retainedCount retainedDegree retainedMass
    retained_nonzero retained_degree retainedReaders retainedCount_unary retainedDegree_binary retainedMass_binary

noncomputable def tablePrepare : List Bool → List Bool := integerTable ∘ prepare

theorem tablePrepareEvaluator : SpaceFunction tablePrepare := prepareEvaluator.chain integerTableEvaluator

theorem retained_prepared_polynomial (bits : List Bool) (i : ℕ) (hi : i<count bits) :
    retainedFamily.polynomial (pair (prepare bits) (BinaryNatCode.encode i)) =
      dyadicFamily.specialized (pair bits (BinaryNatCode.encode i)) := by
  change checkedFamily.polynomial (retainedInput (pair (prepare bits) (BinaryNatCode.encode i))) = _
  simp only [retainedInput, prepare, Function.comp_apply, gcdPrepare, pairFst_pair, pairSnd_pair]
  exact prepared_polynomial bits i hi

end LeanCanny.ETR.CoerciveIntegerPreparation
