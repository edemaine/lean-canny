/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratum
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
public import LeanCanny.Algebra.FixedWidthKroneckerSpace
public import LeanCanny.Algebra.FixedWidthBivariateRowSpace
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
public import LeanCanny.Algebra.PolynomialBinaryProductSpace
public import LeanCanny.Algebra.PolynomialSumSquaresSpace
public import LeanCanny.Algebra.ModularResidueSpace
/-! # Closed native coefficients of the actual compact joint stratum

Only fixed-width queries are serialized. The feature product and stratum
remain implicit, and every caller modulus is retained.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointStratumNative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MatrixPower MvPolynomial
open RationalSubstitution.IntegerBits (context selectedDegree)
open FormulaSignSlotRadialJointStratum
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointCoefficientCatalogue.family
local notation "FA" => FormulaSignSlotRadialJointCoefficientCatalogue.access
attribute [local irreducible] core coefficient polynomial lower upper reciprocalRow width degree productDegree productMass
  FormulaSignSlotRadialJointCore.equation

theorem scalar_packet (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (c bits modulus : List Bool) :
    IntegralOriginalTermCoefficientBits.scalar (A ∘ pairFst) (W ∘ pairFst)
      (fun z => Nat.fromBitsLE (pairSnd z)+1) (fun z => p (pairFst z)) (pair (pair c modulus) bits)=
      residueBits (((p c).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c)
        (Nat.fromBitsLE bits))) : ZMod (Nat.fromBitsLE modulus+1)) := by
  simp only [IntegralOriginalTermCoefficientBits.scalar,Function.comp_apply,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun d M => residueBits (((p d).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE bits))) :
      ZMod M))
    (show pairFst (pairFst (pair (pair c modulus) bits))=c from by rw [pairFst_pair,pairFst_pair])
    (show Nat.fromBitsLE (pairSnd (pairFst (pair (pair c modulus) bits)))+1=Nat.fromBitsLE modulus+1 from by
      rw [pairFst_pair,pairSnd_pair])

theorem packed_packet (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (c bits modulus : List Bool) :
    PrimitivePairBits.coefficient (fun z => FixedWidthKronecker.encode (A z) (W z) (p z))
      (pair (pair c bits) modulus)=residueBits
        ((((FixedWidthKronecker.encode (A c) (W c) (p c)).coeff (Nat.fromBitsLE bits)) : ℤ) :
          ZMod (Nat.fromBitsLE modulus+1)) := by
  simp only [PrimitivePairBits.coefficient,context,selectedDegree,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun d M => residueBits
    ((((FixedWidthKronecker.encode (A d) (W c) (p d)).coeff (Nat.fromBitsLE bits)) : ℤ) :
      ZMod M))
    (show pairFst (pairFst (pair (pair c bits) modulus))=c from by rw [pairFst_pair,pairFst_pair])
    (show Nat.fromBitsLE (pairSnd (pair (pair c bits) modulus))+1=Nat.fromBitsLE modulus+1 from by rw [pairSnd_pair])

theorem row_packet (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (c bits modulus : List Bool) :
    FixedWidthRowBits.value (A ∘ context) (W ∘ context) (fun z => p (context z)) selectedDegree pairSnd
      (pair (pair c bits) modulus)=residueBits (((p c).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE bits))) :
          ZMod (Nat.fromBitsLE modulus+1)) := by
  simp only [FixedWidthRowBits.value,Function.comp_apply,context,selectedDegree,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun d M => residueBits (((p d).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE bits))) :
      ZMod M))
    (show pairFst (pairFst (pair (pair c bits) modulus))=c from by rw [pairFst_pair,pairFst_pair])
    (show Nat.fromBitsLE (pairSnd (pair (pair c bits) modulus))+1=Nat.fromBitsLE modulus+1 from by rw [pairSnd_pair])

theorem castSucc_row (A W : List Bool → ℕ) (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (target modulus : List Bool → List Bool) (hA : UnaryFn A) (hW : UnaryFn W)
    (ht : target ∈ FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p
      (FixedWidthEmbeddingBits.word A (fun c => A c+1) W target pairSnd) modulus)) :
    SpaceFunction (FixedWidthRowBits.value (fun c => A c+1) W
      (fun c => rename Fin.castSucc (p c)) target modulus) :=
  FixedWidthEmbeddingBits.evaluator A (fun c => A c+1) W target pairSnd p
    (fun _ => Fin.castSucc) (fun c => Fin.castSucc_injective (A c))
    (fun c i => pairSnd_pair c (BinaryNatCode.encode i.val)) modulus
    hA (hA.add (UnaryFn.const 1)) hW ht pairSnd_mem_FP E

theorem core_row (read target modulus : List Bool → List Bool)
    (hr : read ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (arity ∘ read) (width ∘ read)
      (fun c => core (read c)) target modulus) := by
  let A := fun z => arity (read (pairFst z))
  let W := fun z => width (read (pairFst z))
  let M := fun z => Nat.fromBitsLE (pairSnd z)+1
  let term := fun z => FormulaSignSlotRadialJointCore.equation (header (read (pairFst z)))
  let word := fun z => (term z).toData.toBits
  have HT : word ∈ FP := mem_FP_comp
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hr) header_FP)
    FormulaSignSlotRadialJointCore.equation_FP
  have E := IntegralOriginalTermCoefficientBits.evaluator A W M
    (arity_unary.comp (mem_FP_comp pairFst_mem_FP hr))
    (width_unary.comp (mem_FP_comp pairFst_mem_FP hr))
    ((BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)) (fun _ => by dsimp [M]; omega)
    (fun z => core (read (pairFst z))) word HT
    (fun z => by
      simp only [word,TermView.term_toBits]
      exact (FormulaSignSlotRadialJointCore.scope _).trans (Nat.le_succ _))
    (fun _ => by simp only [word,TermView.term_toBits]; unfold core; rfl)
  have EQ := E.precompose (fun c => pair (pair c (modulus c)) (target c))
    (mem_FP_pair (mem_FP_pair id_mem_FP hm) ht)
  exact EQ.congr (funext fun c => by
    exact scalar_packet (arity ∘ read) (width ∘ read) (fun z => core (read z)) c (target c) (modulus c))

theorem coefficient_row (read target modulus : List Bool → List Bool)
    (hr : read ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (K : List Bool → ℕ) (hK : BinaryFn K) :
    SpaceFunction (FixedWidthRowBits.value (arity ∘ read) (width ∘ read)
      (fun c => coefficient (read c) (K c)) target modulus) := by
  let A := oldArity ∘ read
  let N := arity ∘ read
  let U := SquareFeatureProductFamily.width F ∘ header ∘ read
  let V := width ∘ read
  let keep := FixedWidthEmbeddingBits.word A N V target pairSnd
  let repack := FixedWidthQuery.repack A V A U keep
  have HA : UnaryFn A := oldArity_unary.comp hr
  have HN : UnaryFn N := arity_unary.comp hr
  have HU : UnaryFn U := (SquareFeatureProductFamily.width_unary F FA).comp (mem_FP_comp hr header_FP)
  have HV : UnaryFn V := width_unary.comp hr
  have HK : keep ∈ FP := FixedWidthEmbeddingBits.word_FP A N V target pairSnd HA HN HV ht pairSnd_mem_FP
  have HR : repack ∈ FP := FixedWidthQuery.repack_mem_FP HA HV HA HU HK
  have E := FixedWidthBivariateRowBits.evaluator (F).arity (SquareFeatureProductFamily.width F)
    (SquareFeatureCoefficientReader.separate F) (SquareFeatureCoefficientReader.reader F FA)
    (FA).arity (SquareFeatureProductFamily.width_unary F FA)
    (fun c k => SquareFeatureCoefficientReader.coefficient_fit F c k)
    (header ∘ read) (mem_FP_comp hr header_FP) K hK repack modulus HR hm
  have EB := FixedWidthRowReboxBits.evaluator A U V keep
    (fun c => SquareFeatureCoefficientReader.coefficient F (header (read c)) (K c)) modulus
    HA HU HV HK (fun _ => SquareFeatureCoefficientReader.coefficient_fit F _ _) E
  have EE := castSucc_row A V
    (fun c => SquareFeatureCoefficientReader.coefficient F (header (read c)) (K c)) target modulus HA HV ht EB
  unfold coefficient
  exact EE

noncomputable def packed (p : (c : List Bool) → MvPolynomial (Fin (arity c)) ℤ)
    (c : List Bool) : Polynomial ℤ := FixedWidthKronecker.encode (arity c) (width c) (p c)

theorem pack (p : (c : List Bool) → MvPolynomial (Fin (arity c)) ℤ)
    (hp : ∀ c, (p c).totalDegree ≤ degree c)
    (E : SpaceFunction (FixedWidthRowBits.value (arity ∘ context) (width ∘ context)
      (fun c => p (context c)) selectedDegree pairSnd)) :
    SpaceFunction (PrimitivePairBits.coefficient (packed p)) :=
  FixedWidthKroneckerBits.evaluator (arity ∘ context) (width ∘ context) (degree ∘ context)
    (fun c => p (context c)) selectedDegree pairSnd
    (arity_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
    (width_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP (fun c => hp (context c))
    (fun c => degree_fit (context c)) E

theorem core_packed : SpaceFunction (PrimitivePairBits.coefficient (packed core)) :=
  pack core (fun c => (core_degree c).trans (by unfold degree; omega))
    (core_row context selectedDegree pairSnd RationalSubstitution.IntegerBits.context_mem_FP
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)

theorem upper_packed : SpaceFunction (PrimitivePairBits.coefficient (packed upper)) := by
  apply pack upper (fun c => (show (upper c).totalDegree ≤ productDegree c from by unfold upper; exact coefficient_degree c _).trans
    (by unfold degree; omega))
  unfold upper
  exact coefficient_row context selectedDegree pairSnd RationalSubstitution.IntegerBits.context_mem_FP
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
      (selected ∘ context) (selected_binary.comp RationalSubstitution.IntegerBits.context_mem_FP)

theorem lower_packed : SpaceFunction (PrimitivePairBits.coefficient (packed lower)) := by
  have HS : BinaryFn (fun c => selected (context c)) := selected_binary.comp RationalSubstitution.IntegerBits.context_mem_FP
  have EC := coefficient_row context selectedDegree pairSnd RationalSubstitution.IntegerBits.context_mem_FP
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
    (fun c => selected (context c)-1)
    (HS.sub (BinaryFn.const 1))
  have EZ : SpaceFunction (FixedWidthRowBits.value (arity ∘ context) (width ∘ context)
      (fun _ => 0) selectedDegree pairSnd) :=
    (SpaceFunction.ofFP _ (constFn_mem_FP [])).congr (funext fun _ => by
      simp [FixedWidthRowBits.value,residueBits,BinaryNatCode.encode])
  have E := FixedWidthRowBits.branch_evaluator (arity ∘ context) (width ∘ context)
    (fun _ => 0) (fun c => coefficient (context c) (selected (context c)-1)) selectedDegree pairSnd
    (fun c => selected (context c)=0)
    (HS.eq (BinaryFn.const 0)) EZ EC
  apply pack lower (fun c => (lower_degree c).trans (by unfold degree; omega))
  simpa only [lower] using E

noncomputable def lastVariable (c : List Bool) : MvPolynomial (Fin (arity c)) ℤ := X (Fin.last (oldArity c))

theorem variable_packed : SpaceFunction (PrimitivePairBits.coefficient (packed lastVariable)) :=
  pack lastVariable (fun c => by simp only [lastVariable,MvPolynomial.totalDegree_X]; unfold degree; omega)
    (FixedWidthRowBits.variable_evaluator (arity ∘ context) (width ∘ context)
      (fun c => Fin.last (oldArity (context c))) selectedDegree pairSnd
      (arity_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
      (width_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
      (oldArity_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
      RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)

theorem add_packed (p q : List Bool → Polynomial ℤ)
    (EP : SpaceFunction (PrimitivePairBits.coefficient p)) (EQ : SpaceFunction (PrimitivePairBits.coefficient q)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => p c+q c)) := by
  have E := ModularResidueSpace.addEvaluator pairSnd
    (fun c => (((p (context c)).coeff (Nat.fromBitsLE (selectedDegree c))) : ZMod (Nat.fromBitsLE (pairSnd c)+1)))
    (fun c => (((q (context c)).coeff (Nat.fromBitsLE (selectedDegree c))) : ZMod (Nat.fromBitsLE (pairSnd c)+1)))
    pairSnd_mem_FP EP EQ
  exact E.congr (funext fun c => by
    simp only [PrimitivePairBits.coefficient,RationalSubstitution.IntegerBits.coefficientResidue,
      Polynomial.coeff_add,Int.cast_add])

theorem neg_packed (p : List Bool → Polynomial ℤ) (EP : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => -p c)) := by
  have E := ModularResidueSpace.negEvaluator pairSnd
    (fun c => (((p (context c)).coeff (Nat.fromBitsLE (selectedDegree c))) : ZMod (Nat.fromBitsLE (pairSnd c)+1)))
    pairSnd_mem_FP EP
  exact E.congr (funext fun c => by
    simp only [PrimitivePairBits.coefficient,RationalSubstitution.IntegerBits.coefficientResidue,
      Polynomial.coeff_neg,Int.cast_neg])

theorem one_packed : SpaceFunction (PrimitivePairBits.coefficient (fun _ => (1 : Polynomial ℤ))) := by
  have HP := (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP).eq (BinaryFn.const 0)
  have HO : (fun c => ArithmeticBits.one (BinaryNat.succ (pairSnd c))) ∈ FP :=
    mem_FP_comp (f := fun c => BinaryNat.succ (pairSnd c)) (g := ArithmeticBits.one)
      (mem_FP_comp (f := pairSnd) (g := BinaryNat.succ) pairSnd_mem_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  have E := SpaceFunction.branch (fun c => decide (Nat.fromBitsLE (selectedDegree c)=0)) HP.flag_mem_FP
    (SpaceFunction.ofFP _ HO) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun c => by
    unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
    by_cases HC : Nat.fromBitsLE (selectedDegree c)=0
    · simp only [HC,decide_true,ite_true,Polynomial.coeff_one_zero,Int.cast_one]
      rw [BinaryNat.succ_eq_bits]
      exact ArithmeticBits.one_residueBits _
    · simp only [HC,decide_false,Bool.false_eq_true,ite_false,Polynomial.coeff_one,Int.cast_zero,
        residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits])

theorem polynomial_packed : SpaceFunction (PrimitivePairBits.coefficient (packed polynomial)) := by
  have EC := PolynomialSumSquaresBits.square_evaluator (packed core) core_packed
  have EL := PolynomialSumSquaresBits.square_evaluator (packed lower) lower_packed
  have EW := PolynomialSumSquaresBits.square_evaluator (packed lastVariable) variable_packed
  have EM := PolynomialBinaryProductBits.evaluator (packed upper) (fun c => packed lastVariable c^2) upper_packed EW
  have ER := add_packed _ _ EM (neg_packed _ one_packed)
  have ES := PolynomialSumSquaresBits.square_evaluator _ ER
  have EA := add_packed _ _ (add_packed _ _ EC EL) ES
  exact EA.congr (funext fun c => by
    simp only [PrimitivePairBits.coefficient,packed,polynomial,reciprocalRow,lastVariable,
      map_add,map_pow,map_mul,map_one,map_neg,sub_eq_add_neg])

noncomputable def value (c : List Bool) : List Bool :=
  FixedWidthRowBits.value (arity ∘ context) (width ∘ context)
    (fun q => polynomial (context q)) selectedDegree pairSnd c

theorem evaluator : SpaceFunction value := by
  let query := fun c => pair (pair (context c)
    (FixedWidthBivariateRowBits.rankCode (arity ∘ context) (width ∘ context) selectedDegree c)) (pairSnd c)
  have HQ : query ∈ FP := mem_FP_pair
    (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
      (mem_FP_comp (FixedWidthQuery.repack_mem_FP
        (arity_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
        (width_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
        (arity_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
        (width_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)
        RationalSubstitution.IntegerBits.selectedDegree_mem_FP) BinaryNat.normalize_mem_FP)) pairSnd_mem_FP
  have E := polynomial_packed.precompose query HQ
  exact E.congr (funext fun c => by
    change PrimitivePairBits.coefficient (packed polynomial) (query c)=_
    rw [show query c=pair (pair (context c)
      (FixedWidthBivariateRowBits.rankCode (arity ∘ context) (width ∘ context) selectedDegree c)) (pairSnd c) from rfl]
    unfold packed
    rw [packed_packet arity width polynomial]
    simp only [FixedWidthBivariateRowBits.rankCode,BinaryNat.normalize_eq_bits,Nat.fromBitsLE_bits]
    change residueBits _=residueBits _
    exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (pairSnd c)+1)))
      (FixedWidthBivariateRowBits.coefficient_repack (arity ∘ context) (width ∘ context)
        (fun q => polynomial (context q)) selectedDegree c ((polynomial_degree _).trans_lt (degree_fit _))))

noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := arity_unary
  width := width_unary
  degree := degree_binary
  mass := mass_binary
  coefficient := value
  evaluator := evaluator
  packet c bits modulus := row_packet arity width polynomial c bits modulus

end LeanCanny.Encoding.FormulaSignSlotRadialJointStratumNative
